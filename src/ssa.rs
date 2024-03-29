use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

pub use crate::{
	iloc::{Block, Function, IlocProgram, Instruction, Operand, Reg},
	label::OrdLabel,
	lcm::{find_loops, lazy_code_motion, postorder, print_maps, reverse_postorder},
};

mod dbre;
pub mod dce;
mod fold;

pub use dbre::{dom_val_num, RenameMeta};
use dce::dead_code;
use fold::{const_fold, ConstMap, ValueKind, WorkStuff};

#[derive(Clone, Debug, Default)]
pub struct ControlFlowGraph {
	paths: HashMap<String, BTreeSet<OrdLabel>>,
	/// After `build_cfg` this will only ever be one `.E_exit` since this is used to merge all
	/// actual exit blocks to a single exit.
	exits: Vec<OrdLabel>,
}

impl ControlFlowGraph {
	/// Adds an edge to our control flow graph.
	pub fn add_edge(&mut self, from: &str, to: &str, sort: isize) {
		self.paths.entry(from.to_string()).or_default().insert(OrdLabel::new_add(sort, to));
	}
}

pub fn build_cfg(func: &mut Function) -> ControlFlowGraph {
	let mut cfg = ControlFlowGraph::default();
	// Add the entry block to the label cache
	let _save_the_label = OrdLabel::new_add(0, ".E_entry");
	func.blocks.insert(0, Block::enter());

	let mut dead = BTreeSet::new();
	'block: for (idx, block) in func.blocks.iter().enumerate() {
		let b_label = &block.label;

		let mut sort = 1;
		let mut unreachable = false;
		'inst: for inst in &block.instructions {
			// N.B.
			// `build_stripped_cfg` in the `dce` mod takes care of all cleaning unreachable code
			if inst.is_return() && !dead.contains(b_label.as_str()) {
				cfg.exits.push(if idx == 0 {
					OrdLabel::new_add(0, b_label)
				} else {
					OrdLabel::from_known(b_label)
				});
				unreachable = true;
				continue 'inst;
			}

			if let Some(label) = inst.uses_label() {
				if unreachable {
					let _save_the_label = OrdLabel::new_add(sort, label);
				} else {
					cfg.add_edge(b_label, label, sort);
				}

				sort += 1;

				// Skip the implicit branch to the block below the current one
				// since we found an unconditional jump.
				//
				// N.B.
				// `build_stripped_cfg` in the `dce` mod takes care of all cleaning unreachable code
				if inst.unconditional_jmp() {
					if unreachable {
						dead.insert(label);
					}
					unreachable = true;
					continue 'inst;
				}
			}
		}

		if let Some(next) = func.blocks.get(idx + 1) {
			let next_label = &next.label;
			if !unreachable {
				cfg.add_edge(b_label, next_label, 0);
			} else {
				let _save_the_label = OrdLabel::new_add(sort, next_label);
			}
		}
	}

	// N.B.
	// `build_stripped_cfg` in the `dce` mod takes care of all cleaning unreachable code
	//
	// Remove unreachable blocks from the cf graph
	// for blk in dead {
	//     let Some(blk_idx) = func.blocks.iter().position(|b| b.label == blk) else { continue; };
	//     func.blocks.remove(blk_idx);
	// }

	let exits: Vec<_> = cfg.exits.drain(..).collect();
	for exit in exits {
		cfg.add_edge(exit.as_str(), ".E_exit", 1);
	}
	cfg.exits.push(OrdLabel::from_known(".E_exit"));
	func.blocks.push(Block::exit());

	cfg
}

#[derive(Debug)]
pub struct DominatorTree {
	/// Dominator frontiers are the join points of a graph, this is not necessarily the
	/// direct predecessors of a block but it will always be a join of two
	/// predecessors into one.
	pub dom_frontier_map: HashMap<OrdLabel, BTreeSet<OrdLabel>>,
	post_dom_frontier: HashMap<OrdLabel, BTreeSet<OrdLabel>>,
	post_idom_map: HashMap<OrdLabel, OrdLabel>,
	pub dom_tree: HashMap<OrdLabel, BTreeSet<OrdLabel>>,
	pub cfg_succs_map: HashMap<OrdLabel, BTreeSet<OrdLabel>>,
	pub cfg_preds_map: HashMap<OrdLabel, BTreeSet<OrdLabel>>,
}

pub fn dominator_tree(cfg: &ControlFlowGraph, blocks: &mut [Block]) -> DominatorTree {
	let start = OrdLabel::entry();
	let exit = OrdLabel::exit();

	let succs = cfg
		.paths
		.iter()
		.map(|(k, v)| (OrdLabel::from_known(k), v.clone()))
		.collect::<HashMap<_, _>>();
	for (ord, n) in reverse_postorder(&succs, &start).into_iter().enumerate() {
		// Updates the global map that keeps track of a labels order in the graph
		OrdLabel::update(ord as isize, n.as_str());
	}

	// We need this to be accurate to the numbering of `succs` below, otherwise
	// when ralloc needs SSA numbering we crash, since the last value for `start` was the
	// last from doing postorder.
	let start = OrdLabel::from_known(start.as_str());
	let succs: HashMap<_, BTreeSet<OrdLabel>> = cfg
		.paths
		.iter()
		.map(|(k, v)| {
			(OrdLabel::from_known(k), v.iter().map(|l| OrdLabel::from_known(l.as_str())).collect())
		})
		.collect();
	let mut preds: HashMap<_, BTreeSet<_>> = HashMap::new();
	for (from, set) in &succs {
		for to in set {
			preds.entry(to.clone()).or_default().insert(from.clone());
		}
	}

	// Build dominator tree
	let mut dom_map = HashMap::with_capacity(blocks.len());
	let all_nodes: Vec<_> = reverse_postorder(&succs, &start).into_iter().cloned().collect();
	dom_map.insert(start.clone(), BTreeSet::new());
	for n in all_nodes.iter().skip(1) {
		dom_map.insert(n.clone(), all_nodes.iter().cloned().collect());
	}
	let mut changed = true;
	while changed {
		changed = false;
		for n in all_nodes.iter() {
			let sets = preds
				.get(n)
				.unwrap_or(&BTreeSet::new())
				.iter()
				.flat_map(|p| dom_map.get(p))
				.collect::<Vec<_>>();
			let mut new_dom = dom_map.get(n).unwrap().clone();
			for set in sets {
				new_dom = new_dom.intersection(set).cloned().collect();
			}

			new_dom.insert(n.clone());

			if Some(&new_dom) != dom_map.get(n) {
				dom_map.insert(n.clone(), new_dom);
				changed = true;
			}
		}
	}

	let mut dom_tree: HashMap<_, BTreeSet<_>> = HashMap::with_capacity(all_nodes.len());
	for set in dom_map.values() {
		let mut tree_leaf: Option<&OrdLabel> = None;
		for m in set {
			if let Some(t) = &mut tree_leaf {
				dom_tree.entry(t.clone()).or_default().insert(m.clone());
				*t = m;
			} else {
				tree_leaf = Some(m);
			}
		}
	}

	// print_maps("dom_map", dom_map.iter());
	// print_maps("cfg_preds", preds.iter());

	// Build dominance predecessor map (AKA find join points)
	let mut dom_tree_pred = HashMap::with_capacity(all_nodes.len());
	for (to, set) in &dom_tree {
		for from in set {
			dom_tree_pred.entry(from.clone()).or_insert_with(BTreeSet::new).insert(to.clone());
		}
	}

	// print_maps("dom_preds", dom_tree_pred.iter());

	let mut idom_map = HashMap::with_capacity(all_nodes.len());
	for node in &all_nodes {
		let mut labels = VecDeque::from([node]);
		while let Some(dfset) = labels.pop_front().and_then(|l| dom_tree_pred.get(l)) {
			if dfset.len() == 1 {
				idom_map.insert(node, (*dfset.iter().next().unwrap()).clone());
				break;
			} else {
				panic!("multiple immediate dominators for {:?}", (dfset, node))
			}
		}
	}

	// print_maps("idom", idom_map.iter());

	let empty = BTreeSet::new();
	// Keith Cooper/Linda Torczon EaC pg. 499 SSA dominance frontier algorithm
	//
	// This is a mapping of node -> descendent in graph that is join point for this node
	// (anytime the graph makes the lower half of a diamond)
	let mut dom_frontier_map: HashMap<OrdLabel, BTreeSet<OrdLabel>> =
		HashMap::with_capacity(all_nodes.len());
	for node in &all_nodes {
		let parents = preds.get(node).unwrap_or(&empty);
		// Node must be a join point (have multiple preds)
		if parents.len() > 1 {
			// For each previous node find a predecessor of `node` that also dominates
			// `node`
			for p in parents {
				let mut run = p;
				// Until we hit an immediate dominator
				while Some(run) != idom_map.get(node) {
					// We add all the blocks that meet at `run`
					// If 0 -> 1 and 2 -> 1 then 1'a dom frontier is `1: {0, 2}`
					dom_frontier_map.entry(run.clone()).or_default().insert(node.clone());
					if let Some(idom) = idom_map.get(run) {
						run = idom;
					} else {
						println!("no idom found for: {run}");
						break;
					}
				}
			}
		}
	}

	// print_maps("dom_frontier", dom_frontier_map.iter());

	// Reorder the numbering on each block so they are reversed
	let all_nodes: Vec<_> = postorder(&succs, &start)
		.into_iter()
		.enumerate()
		.map(|(i, l)| {
			OrdLabel::update(i as isize, l.as_str());
			OrdLabel::from_known(l.as_str())
		})
		.collect();

	let mut post_dom = HashMap::<_, BTreeSet<_>>::with_capacity(all_nodes.len());
	// Stick all the exit block in with empty post dom sets
	post_dom.extend(cfg.exits.iter().map(|e| (OrdLabel::from_known(e.as_str()), BTreeSet::new())));
	for n in all_nodes.iter().skip(1) {
		post_dom.insert(n.clone(), all_nodes.iter().cloned().collect());
	}
	let mut changed = true;
	while changed {
		changed = false;
		for n in all_nodes.iter() {
			let sets = succs
				.get(n)
				.unwrap_or(&BTreeSet::new())
				.iter()
				.flat_map(|p| post_dom.get(p))
				.collect::<Vec<_>>();
			let Some(mut new_dom) = post_dom.get(n).cloned() else { println!("no post dom found {n}"); continue; };
			// let mut new_dom = post_dom.get(n).unwrap().clone();
			for set in sets {
				new_dom = new_dom.intersection(set).cloned().collect();
			}

			new_dom.insert(n.clone());

			if Some(&new_dom) != post_dom.get(n) {
				post_dom.insert(n.clone(), new_dom);
				changed = true;
			}
		}
	}
	// This is just postdominators tree
	let mut post_dom_tree: HashMap<OrdLabel, BTreeSet<OrdLabel>> =
		HashMap::with_capacity(all_nodes.len());
	for ord_path in all_nodes.iter().filter_map(|n| post_dom.get(n)) {
		let mut last: Option<&OrdLabel> = None;
		for blk in ord_path.iter() {
			if let Some(last_blk) = &mut last {
				post_dom_tree.entry(last_blk.clone()).or_default().insert(blk.clone());
				*last_blk = blk;
			} else {
				last = Some(blk);
			}
		}
	}

	let mut post_dom_tree_preds = HashMap::<_, BTreeSet<_>>::with_capacity(all_nodes.len());
	for (f, pd) in &post_dom_tree {
		for t in pd {
			post_dom_tree_preds.entry(t.clone()).or_default().insert(f.clone());
		}
	}
	let mut post_idom_map = HashMap::with_capacity(all_nodes.len());
	for node in &all_nodes {
		let mut labels = VecDeque::from([node]);
		while let Some(pdfset) = labels.pop_front().and_then(|l| post_dom_tree_preds.get(l)) {
			if pdfset.len() == 1 {
				post_idom_map.insert(node.clone(), (*pdfset.first().unwrap()).clone());
				break;
			}
			labels.extend(pdfset);
		}
	}

	// print_maps("dom_tree", dom_tree.iter());
	// print_maps("dom_frontier_map", dom_frontier_map.iter());

	// print_maps("post_idom", post_idom_map.iter());
	// print_maps("post_dom_tree", post_dom_tree.iter());

	let empty = BTreeSet::new();
	// This is control dependence
	let mut post_dom_frontier = HashMap::<_, BTreeSet<OrdLabel>>::with_capacity(all_nodes.len());
	for node in &all_nodes {
		// This is post dominator frontier
		// This includes 1 -> 2 __and__ 1 -> 5 (the graph from his notes
		// and similar to https://pages.cs.wisc.edu/~fischer/cs701.f08/lectures/Lecture19.4up.pdf slide 6)
		//
		let kids = succs.get(node).unwrap_or(&empty);
		if kids.len() > 1 {
			for p in kids {
				let r = OrdLabel::from_known(p.as_str());
				// We have to use the updated label orderings or we get duplicates
				let mut run = &r;
				while Some(run) != post_idom_map.get(node) {
					// This is node_a -> node_b (that controls execution of `node_a`)
					post_dom_frontier.entry(run.clone()).or_default().insert(node.clone());
					if let Some(idom) = post_idom_map.get(run) {
						run = idom;
					}
				}
			}
		}
	}
	// Carr's isn't the same as post dominator frontier...
	// It misses 1 -> 5 (see above)

	// print_maps("pdf", post_dom_frontier.iter());

	DominatorTree {
		dom_frontier_map,
		post_dom_frontier,
		post_idom_map,
		dom_tree,
		cfg_preds_map: preds,
		cfg_succs_map: succs,
	}
}

pub fn insert_phi_functions(
	func: &mut Function,
	cfg_succs: &HashMap<OrdLabel, BTreeSet<OrdLabel>>,
	dom_front: &HashMap<OrdLabel, BTreeSet<OrdLabel>>,
) -> BTreeMap<OrdLabel, BTreeSet<Reg>> {
	let start = OrdLabel::entry();

	// All the registers that are used across blocks
	let mut globals = vec![];
	let mut blocks_map = HashMap::new();
	let mut varkill = BTreeMap::new();
	let mut upvar = BTreeMap::new();
	// TODO: now that I do this bottom-up phis could be inserted as each block is
	// encountered since we know dom frontier
	for blk in postorder(cfg_succs, &start) {
		// This represents any redefinitions that are local to the current block
		let mut varkil = BTreeSet::new();
		let mut upv = BTreeSet::new();
		for inst in func
			.blocks
			.iter()
			.find(|b| b.label == blk.as_str())
			.map_or(&[] as &[_], |b| &b.instructions)
		{
			let (a, b) = inst.operands();
			if let Some(Operand::Register(a)) = a {
				if !varkil.contains(&a) {
					blocks_map.entry(a).or_insert_with(BTreeSet::new).insert(blk.clone());
					globals.push(a);
					upv.insert(a);
				}
			}
			if let Some(Operand::Register(b)) = b {
				if !varkil.contains(&b) {
					blocks_map.entry(b).or_insert_with(BTreeSet::new).insert(blk.clone());
					globals.push(b);
					upv.insert(b);
				}
			}
			if let Some(dst) = inst.target_reg() {
				varkil.insert(*dst);
				blocks_map.entry(*dst).or_insert_with(BTreeSet::new).insert(blk.clone());
			}
		}

		varkill.insert(blk.clone(), varkil);
		upvar.insert(blk.clone(), upv);
	}

	let empty = BTreeSet::new();
	let mut changed = true;
	let mut live_in: BTreeMap<_, BTreeSet<Reg>> = BTreeMap::new();
	let mut live_out: BTreeMap<_, BTreeSet<Reg>> = BTreeMap::new();
	while changed {
		changed = false;
		for label in postorder(cfg_succs, &start) {
			let live_def_diff = live_out
				.get(label)
				.unwrap_or(&empty)
				.difference(varkill.get(label).unwrap_or(&empty))
				.copied()
				.collect();

			// PhiDef(b) ∪ UpExpr(b) ∪ (LiveOut(b) - Defs(b))
			let new = upvar.get(label).unwrap_or(&empty).union(&live_def_diff).copied().collect();
			let old = live_in.entry(label.clone()).or_default();
			if *old != new {
				*old = new;
				changed |= true;
			}

			let mut new = cfg_succs
				.get(label) // TODO: filter exit node out
				.unwrap_or(&BTreeSet::new())
				.iter()
				.map(|s| live_in.get(s).unwrap_or(&empty))
				.fold(BTreeSet::new(), |collect, next| collect.union(next).copied().collect());

			let curr = live_out.entry(label.clone()).or_default();
			if new != *curr {
				changed = true;
				*curr = new;
			}
		}
	}

	// print_maps("liveout", live_out.iter());
	// print_maps("livein", live_in.iter());

	let empty_label = BTreeSet::new();
	let mut phis: BTreeMap<_, BTreeSet<_>> = BTreeMap::new();
	for global_reg in &globals {
		let mut worklist =
			blocks_map.get(global_reg).unwrap_or(&empty_label).iter().collect::<VecDeque<_>>();
		// For every block that this variable is live in
		while let Some(blk) = worklist.pop_front() {
			// The dominance frontier (join point) is the block that needs
			// the 𝛟 added to it
			for d in dom_front.get(blk).unwrap_or(&empty_label) {
				// If we have seen this register or it isn't in the current block we are
				// checking skip it
				if !phis.get(d).map_or(false, |set| set.contains(global_reg))
					&& live_in.get(d).map_or(false, |set| set.contains(global_reg))
				{
					// insert phi func
					phis.entry(d.clone()).or_default().insert(*global_reg);
					// Add the dom frontier node to the `worklist`
					worklist.push_back(d);
				}
			}
		}
	}

	for (label, set) in &phis {
		// if label.as_str() == ".E_exit" {
		//     continue;
		// }
		let blk = func.blocks.iter_mut().find(|b| b.label == label.as_str()).unwrap();
		// If the block starts with a frame and label skip it other wise just skip a label
		let index = if let Instruction::Frame { .. } = &blk.instructions[0] { 2 } else { 1 };
		for reg in set {
			blk.instructions.insert(index, Instruction::new_phi(*reg));
		}
	}

	phis
}

pub fn ssa_optimization(iloc: &mut IlocProgram) -> HashMap<String, DominatorTree> {
	let mut dom_trees = HashMap::new();
	for func in &mut iloc.functions {
		let cfg = build_cfg(func);

		let start = OrdLabel::entry();
		let dtree = dominator_tree(&cfg, &mut func.blocks);

		// print_maps("cfg_succs", dtree.cfg_preds_map.iter());
		// print_maps("dom_tree", dtree.dom_tree.iter());

		// The `phis` used to fill the `meta` map
		let _phis = insert_phi_functions(func, &dtree.cfg_succs_map, &dtree.dom_frontier_map);

		let mut meta = HashMap::new();
		let mut stack = VecDeque::new();
		dom_val_num(&mut func.blocks, 0, &mut meta, &dtree, &mut stack);

		// TODO: move this and `const_fold` into `dom_val_num` so we aren't repeating
		// the work...
		let mut worklist = VecDeque::default();
		let mut const_vals = ConstMap::default();
		for (b, block) in func.blocks.iter().enumerate() {
			for (i, inst) in block.instructions.iter().enumerate() {
				if let Some(dst) = inst.target_reg() {
					if inst.is_load_imm() {
						let latice = ValueKind::Known(inst.operands().0.unwrap().clone_to_value());
						const_vals.add_def(*dst, latice.clone(), (b, i));
						worklist.push_back(WorkStuff::new(*dst, b, i));
					} else if inst.is_store()
					// TODO: any way around this PLEASE...
						|| matches!(inst, Instruction::I2I { .. } | Instruction::I2F { .. })
					{
						const_vals.add_def(*dst, ValueKind::Unknowable, (b, i))
					} else {
						const_vals.add_def(*dst, ValueKind::Maybe, (b, i))
					}
				}
				match inst.operands() {
					(Some(Operand::Register(a_reg)), Some(Operand::Register(b_reg))) => {
						const_vals.add_use(a_reg, b, i);
						const_vals.add_use(b_reg, b, i);
					}
					(Some(Operand::Register(a)), None) | (None, Some(Operand::Register(a))) => {
						const_vals.add_use(a, b, i);
					}
					_ => {}
				}
			}
		}

		const_fold(&mut worklist, &mut const_vals, func);

		dead_code(func, &dtree, &start);

		dom_trees.insert(func.label.clone(), dtree);
	}

	dom_trees
}

#[test]
fn lcm_pre() {
	use std::{fs, io::Write, path::PathBuf};

	use crate::iloc::{make_basic_blocks, make_blks, parse_text};

	let input_file = "input/sloop.il";

	let input = fs::read_to_string(input_file).unwrap();
	let iloc = parse_text(&input).unwrap();
	let mut blocks = make_basic_blocks(&make_blks(iloc));

	let start = OrdLabel::entry();

	let cfg = build_cfg(&mut blocks.functions[0]);
	let dtree = dominator_tree(&cfg, &mut blocks.functions[0].blocks);

	lazy_code_motion(&mut blocks.functions[0], &dtree);

	let mut buf = String::new();
	for inst in blocks.instruction_iter() {
		if matches!(inst, Instruction::Skip(..)) {
			continue;
		}

		buf.push_str(&inst.to_string())
	}

	let mut path = PathBuf::from(input_file);
	let file = path.file_stem().unwrap().to_string_lossy().to_string();
	path.set_file_name(&format!("{}.pre.il", file));
	let mut fd =
		fs::OpenOptions::new().create(true).truncate(true).write(true).open(&path).unwrap();
	fd.write_all(buf.as_bytes()).unwrap();
}

#[test]
fn ssa_cfg() {
	use std::fs;

	use crate::iloc::{make_basic_blocks, make_blks, parse_text};

	let input = fs::read_to_string("input/partition.il").unwrap();
	let iloc = parse_text(&input).unwrap();
	let mut blocks = make_basic_blocks(&make_blks(iloc));

	let cfg = build_cfg(&mut blocks.functions[0]);
	println!("{:?}", cfg);
	emit_cfg_viz(&cfg, "graphs/partition.dot");
}

#[test]
fn ssa_cfg_while() {
	use std::fs;

	use crate::iloc::{make_basic_blocks, make_blks, parse_text};

	let input = fs::read_to_string("input/hmm.il").unwrap();
	let iloc = parse_text(&input).unwrap();
	let mut blocks = make_basic_blocks(&make_blks(iloc));

	let cfg = build_cfg(&mut blocks.functions[0]);
	// println!("{:?}", cfg);

	emit_cfg_viz(&cfg, "graphs/hmm.dot");

	let name = OrdLabel::entry();
	dominator_tree(&cfg, &mut blocks.functions[0].blocks);
}

#[test]
fn ssa_cfg_dumb() {
	use std::fs;

	use crate::iloc::{make_basic_blocks, make_blks, parse_text};

	let input = fs::read_to_string("input/dumb.il").unwrap();
	let iloc = parse_text(&input).unwrap();
	let mut blocks = make_basic_blocks(&make_blks(iloc));
	ssa_optimization(&mut blocks);
}

#[test]
fn ssa_cfg_trap() {
	use std::fs;

	use crate::iloc::{make_basic_blocks, make_blks, parse_text};

	let input = fs::read_to_string("input/turd.il").unwrap();
	let iloc = parse_text(&input).unwrap();
	let mut blocks = make_basic_blocks(&make_blks(iloc));

	let cfg = build_cfg(&mut blocks.functions[0]);
	let name = OrdLabel::entry();
	let dom = dominator_tree(&cfg, &mut blocks.functions[0].blocks);

	println!("{:#?}", dom);
	// emit_cfg_viz(&cfg, "graphs/turd.dot");
	// dominator_tree(&cfg, &mut blocks.functions[0].blocks);
}

#[test]
fn lcm_simple() {
	use std::fs;

	use crate::iloc::{make_basic_blocks, make_blks, parse_text};

	let input = "
	.data
.text
.frame pre_example, 4, %vr100, %vr200, %vr300
	loadI 4 => %vr4
	i2i %vr4 => %vr5
	loadI 5 => %vr6
	comp %vr100, %vr6 => %vr7
	testge %vr7 => %vr8
	cbr %vr8 -> .L1
.L0: nop
	add %vr200, %vr5 => %vr9
	i2i %vr9 => %vr300
	loadI 1 => %vr10
	add %vr100, %vr10 => %vr11
	i2i %vr11 => %vr100
	loadI 5 => %vr6
	comp %vr100, %vr6 => %vr7
	testge %vr7 => %vr8
	cbrne %vr8 -> .L0
.L1: nop
	iwrite %vr300
	ret
";
	let iloc = parse_text(input).unwrap();
	let mut blocks = make_basic_blocks(&make_blks(iloc));

	let cfg = build_cfg(&mut blocks.functions[0]);
	let name = OrdLabel::entry();
	let dom = dominator_tree(&cfg, &mut blocks.functions[0].blocks);

	lazy_code_motion(&mut blocks.functions[0], &dom);
}
#[allow(unused)]
fn emit_cfg_viz(cfg: &ControlFlowGraph, file: &str) {
	use std::{
		collections::hash_map::DefaultHasher,
		fmt::Write,
		fs,
		hash::{Hash, Hasher},
	};

	fn str_id(s: &str) -> u64 {
		let mut state = DefaultHasher::default();
		s.hash(&mut state);
		state.finish()
	}

	let mut seen = HashSet::new();
	let mut buf = String::new();
	writeln!(buf, "digraph cfg {{").unwrap();
	for (n, map) in &cfg.paths {
		writeln!(buf, "{} [ label = \"{}\", shape = square]", str_id(n), n).unwrap();
		seen.insert(n.as_str());
		for e in map {
			if !seen.contains(e.as_str()) {
				writeln!(buf, "{} [ label = \"{}\", shape = square]", str_id(e.as_str()), e)
					.unwrap();
				seen.insert(e.as_str());
			}
			writeln!(buf, "{} -> {}", str_id(n), str_id(e.as_str())).unwrap();
		}
	}
	writeln!(buf, "}}").unwrap();
	fs::write(file, buf).unwrap();
}
