use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};

use crate::{
    iloc::{Block, Function, IlocProgram, Instruction, Operand},
    lcm::print_maps,
};

mod dbre;
pub mod dce;
mod fold;

pub use crate::{
    label::OrdLabel,
    lcm::{find_loops, lazy_code_motion, postorder, reverse_postorder},
};
pub use dbre::{dom_val_num, RenameMeta};

use dce::dead_code;
use fold::{const_fold, ConstMap, ValueKind, WorkStuff};

#[derive(Clone, Debug, Default)]
pub struct ControlFlowGraph {
    paths: HashMap<String, BTreeSet<OrdLabel>>,
    pub exits: Vec<OrdLabel>,
}

impl ControlFlowGraph {
    /// Adds an edge to our control flow graph.
    pub fn add_edge(&mut self, from: &str, to: &str, sort: isize) {
        self.paths.entry(from.to_string()).or_default().insert(OrdLabel::new_add(sort, to));
    }
}

pub fn build_cfg(func: &mut Function) -> ControlFlowGraph {
    let mut cfg = ControlFlowGraph::default();
    'block: for (idx, block) in func.blocks.iter().enumerate() {
        let b_label = &block.label;

        let mut sort = 1;
        let mut unreachable = false;
        // TODO: only iter the branch instructions with labels
        'inst: for inst in &block.instructions {
            // TODO: can we make note of this for optimization...(if there are trailing
            // unreachable instructions)
            if inst.is_return() {
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
                // TODO: can we make note of this for optimization...(if there are
                // trailing unreachable instructions)
                if inst.unconditional_jmp() {
                    continue 'block;
                }
            }
        }

        if let Some(next) = func.blocks.get(idx + 1) {
            let next_label = &next.label;
            cfg.add_edge(b_label, next_label, 0);
        }
    }

    // Remove unreachable blocks from the cf graph
    // let remove_blks = all.difference(&seen.keys().copied().collect::<BTreeSet<_>>());
    // for blk_idx in remove_blks {
    //     func.blocks.remove(blk_idx);
    // }

    if cfg.exits.len() > 1 {
        let exits: Vec<_> = cfg.exits.drain(..).collect();
        for exit in exits {
            cfg.add_edge(exit.as_str(), ".E_exit", 1);
        }
        cfg.exits.push(OrdLabel::from_known(".E_exit"));

        func.blocks.push(Block::exit());
    }

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

// TODO: Cleanup (see todo's above loops and such)
pub fn dominator_tree(
    cfg: &ControlFlowGraph,
    blocks: &mut [Block],
    start: &OrdLabel,
) -> DominatorTree {
    for (ord, n) in reverse_postorder(
        &cfg.paths.iter().map(|(k, v)| (OrdLabel::new(k), v.clone())).collect::<HashMap<_, _>>(),
        start,
    )
    .enumerate()
    {
        // Updates the global map that keeps track of a labels order in the graph
        OrdLabel::update(ord as isize, n.as_str());
    }

    // We need this to be accurate to the numbering of `succs` below, otherwise
    // when ralloc needs SSA numbering we crash, since the las value for `start` was the
    // last from doing RPO based on predecessors and the single exit
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
    let all_nodes: Vec<_> = reverse_postorder(&succs, &start).cloned().collect();
    dom_map.insert(start, BTreeSet::new());
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

    // Build dominance predecessor map (AKA find join points)
    let mut dom_tree_pred = HashMap::with_capacity(all_nodes.len());
    for (to, set) in &dom_tree {
        for from in set {
            dom_tree_pred.entry(from.clone()).or_insert_with(BTreeSet::new).insert(to.clone());
        }
    }

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

    // println!("tree: {:#?} \ndom_preds: {:#?}\n{:?}", dom_tree, dom_tree_pred, preds);

    let empty = BTreeSet::new();
    // Keith Cooper/Linda Torczon EaC pg. 499 SSA dominance frontier algorithm
    //
    // This is a mapping of node -> descendent in graph that is join point for this node
    // (anytime the graph make the lower half of a diamond)
    let mut dom_frontier_map: HashMap<OrdLabel, BTreeSet<OrdLabel>> =
        HashMap::with_capacity(all_nodes.len());
    for node in &all_nodes {
        let parents = preds.get(node).unwrap_or(&empty);
        // Node must be a join point (have multiple preds)
        if parents.len() > 1 {
            // For each previous node find a predecessor of `label` that also dominates
            // `label
            for p in parents {
                let mut run = p;
                // Until we hit an immediate dominator
                while Some(run) != idom_map.get(node) {
                    // We add all the blocks that meet at `run`
                    // If 0 -> 1 and 2 -> 1 then 1'a dom frontier is `1: {0, 2}`
                    dom_frontier_map.entry(run.clone()).or_default().insert(node.clone());
                    if let Some(idom) = idom_map.get(run) {
                        run = idom;
                    }
                }
            }
        }
    }

    // Reorder the numbering on each block so they are reversed
    let all_nodes: Vec<_> = reverse_postorder(&preds, cfg.exits.first().unwrap())
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
            let mut new_dom = post_dom.get(n).unwrap().clone();
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

    // println!("pid {:#?}", post_idom_map);
    // println!("pdt {:#?}\ndt {:#?}\ndft {:#?}", post_dom_tree, dom_tree,
    // dom_frontier_map);

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
    //
    // for node in postorder(&post_dom_tree, cfg.exits) {
    //     println!("{}", node.as_str());
    //     for c in succs.get(node).unwrap_or(&empty) {
    //         for m in post_dom_frontier.get(c).cloned().unwrap_or_default() {
    //             if !post_dom_tree.get(node).map_or(false, |set| set.contains(&m)) {
    //                 // This is node -> nodes it controls
    //                 //
    // post_dom_frontier.entry(m.clone()).or_default().insert(node.clone());

    //                 // This is node -> nodes that control it (generally nodes above it)
    //
    // post_dom_frontier.entry(node.clone()).or_default().insert(m.clone());
    //             }
    //         }
    //     }
    //     for m in preds.get(node).unwrap_or(&empty) {
    //         // We have to use the updated label orderings or we get duplicates
    //         let m = OrdLabel::from_known(m.as_str());
    //         if !post_dom_tree.get(node).map_or(false, |set| set.contains(&m)) {
    //             // This is node -> nodes it controls
    //             // post_dom_frontier.entry(m).or_default().insert(node.clone());

    //             // This is node -> nodes that control it (generally nodes above it)
    //             post_dom_frontier.entry(node.clone()).or_default().insert(m);
    //         }
    //     }
    // }

    // println!("pdf {:#?}", post_dom_frontier);

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
    start: &OrdLabel,
    dom_front: &HashMap<OrdLabel, BTreeSet<OrdLabel>>,
) -> HashMap<OrdLabel, HashSet<Operand>> {
    // All the registers that are used across blocks
    let mut globals = vec![];
    let mut blocks_map = HashMap::new();

    // TODO: now that I do this bottom-up phis could be inserted as each block is
    // encountered since we know dom frontier
    for blk in postorder(cfg_succs, start) {
        // This represents any redefinitions that are local to the current block
        let mut varkil = HashSet::new();
        for inst in func
            .blocks
            .iter()
            .find(|b| b.label == blk.as_str())
            .map_or(&[] as &[_], |b| &b.instructions)
        {
            let (a, b) = inst.operands();
            let dst = inst.target_reg();
            if let Some(a @ Operand::Register(..)) = a {
                if !varkil.contains(&a) {
                    blocks_map.entry(a.clone()).or_insert_with(HashSet::new).insert(blk);
                    globals.push(a);
                }
            }
            if let Some(b @ Operand::Register(..)) = b {
                if !varkil.contains(&b) {
                    blocks_map.entry(b.clone()).or_insert_with(HashSet::new).insert(blk);
                    globals.push(b);
                }
            }
            if let Some(dst) = dst {
                varkil.insert(Operand::Register(*dst));
                blocks_map.entry(Operand::Register(*dst)).or_insert_with(HashSet::new).insert(blk);
            }
        }
    }

    let empty = HashSet::new();
    let empty_set = BTreeSet::new();
    let mut phis: HashMap<_, HashSet<_>> = HashMap::new();
    for global_reg in &globals {
        let mut worklist =
            blocks_map.get(global_reg).unwrap_or(&empty).iter().copied().collect::<VecDeque<_>>();
        // For every block that this variable is live in
        while let Some(blk) = worklist.pop_front() {
            // The dominance frontier (join point) is the block that needs
            // the 𝛟 added to it
            for d in dom_front.get(blk).unwrap_or(&empty_set) {
                // If we have seen this register or it isn't in the current block we are
                // checking skip it
                if !phis.get(d).map_or(false, |set| set.contains(global_reg))
                    && blocks_map.get(global_reg).map_or(false, |l| l.contains(blk))
                {
                    // insert phi func
                    phis.entry(d.clone()).or_default().insert(global_reg.clone());
                    // Add the dom frontier node to the `worklist`
                    worklist.push_back(d);
                }
            }
        }
    }

    for (label, set) in &phis {
        if label.as_str() == ".E_exit" {
            continue;
        }
        let blk = func.blocks.iter_mut().find(|b| b.label == label.as_str()).unwrap();
        // If the block starts with a frame and label skip it other wise just skip a label
        let index = if let Instruction::Frame { .. } = &blk.instructions[0] { 2 } else { 1 };
        for reg in set {
            blk.instructions.insert(index, Instruction::new_phi(reg.copy_to_register()));
        }
    }

    phis
}

pub fn ssa_optimization(iloc: &mut IlocProgram) {
    for func in &mut iloc.functions {
        let cfg = build_cfg(func);

        let start = OrdLabel::new_start(&func.label);
        let dtree = dominator_tree(&cfg, &mut func.blocks, &start);

        print_maps("cfg_succs", dtree.cfg_succs_map.iter());
        print_maps("dom_tree", dtree.dom_tree.iter());
        // The `phis` used to fill the `meta` map
        let _phis =
            insert_phi_functions(func, &dtree.cfg_succs_map, &start, &dtree.dom_frontier_map);

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

        for blk in &mut func.blocks {
            for inst in &mut blk.instructions {
                inst.remove_phis();
            }
        }

        lazy_code_motion(func, &dtree, cfg.exits.last().unwrap());

        func.blocks.retain(|b| b.label != ".E_exit");
    }
}

#[test]
fn lcm_pre() {
    use std::{fs, io::Write, path::PathBuf};

    use crate::iloc::{make_basic_blocks, make_blks, parse_text};

    let input_file = "input/sloop.il";

    let input = fs::read_to_string(input_file).unwrap();
    let iloc = parse_text(&input).unwrap();
    let mut blocks = make_basic_blocks(&make_blks(iloc));

    let start = OrdLabel::new_start(&blocks.functions[0].label);

    let cfg = build_cfg(&mut blocks.functions[0]);
    let dtree = dominator_tree(&cfg, &mut blocks.functions[0].blocks, &start);

    lazy_code_motion(&mut blocks.functions[0], &dtree, cfg.exits.last().unwrap());

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

    let input = fs::read_to_string("input/while_array.lvn.dbre.dce.pre.il").unwrap();
    let iloc = parse_text(&input).unwrap();
    let mut blocks = make_basic_blocks(&make_blks(iloc));

    let cfg = build_cfg(&mut blocks.functions[0]);
    println!("{:?}", cfg);
    emit_cfg_viz(&cfg, "graphs/while_array.dot");
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

    let name = OrdLabel::new_start(&blocks.functions[0].label);
    dominator_tree(&cfg, &mut blocks.functions[0].blocks, &name);
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
    let name = OrdLabel::new_start(&blocks.functions[0].label);
    let dom = dominator_tree(&cfg, &mut blocks.functions[0].blocks, &name);

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
.frame main, 0
    loadI 4 => %vr4
    loadI 42 => %vr42
    add %vr0, %vr4 => %vr5
    store %vr42 => %vr5
    ret
";
    let iloc = parse_text(input).unwrap();
    let mut blocks = make_basic_blocks(&make_blks(iloc));

    let cfg = build_cfg(&mut blocks.functions[0]);
    let name = OrdLabel::new_start(&blocks.functions[0].label);
    let dom = dominator_tree(&cfg, &mut blocks.functions[0].blocks, &name);

    lazy_code_motion(&mut blocks.functions[0], &dom, cfg.exits.last().unwrap());
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
