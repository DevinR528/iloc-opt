use std::{
    cell::Cell,
    collections::{hash_map::RandomState, BTreeMap, BTreeSet, HashMap, HashSet, VecDeque},
    fmt,
};

use crate::iloc::{Block, Function, IlocProgram, Instruction, Operand};

mod dce;
mod dnre;
mod fold;
mod licm;

use dce::dead_code;
use dnre::{dom_val_num, RenameMeta};
use fold::{const_fold, ConstMap, ValueKind, WorkStuff};
#[allow(unused)]
use licm::find_loops;

#[allow(unused)]
fn print_blocks(blocks: &[Block]) {
    for blk in &*blocks {
        // if !matches!(blk.label.as_str(), ".L0:" | ".L1:" | ".L3:" | ".L7:") {
        //     continue;
        // }

        println!("{} [", blk.label);
        for inst in &blk.instructions {
            println!("  {:?}", inst);
        }
        println!("]");
    }
}

pub fn reverse_postoder(
    succs: &HashMap<String, BTreeSet<String>>,
) -> impl Iterator<Item = &str> + '_ {
    let mut stack = VecDeque::from_iter([".L_main"]);
    let mut seen = HashSet::<_, RandomState>::from_iter([".L_main"]);
    std::iter::from_fn(move || {
        let val = stack.pop_front()?;
        if let Some(set) = succs.get(val) {
            for child in set {
                if seen.contains(child.as_str()) {
                    continue;
                }
                stack.push_back(child)
            }
        }
        seen.insert(val);

        Some(val)
    })
}

#[derive(Clone, Copy, Debug)]
pub enum TraversalState {
    Start,
    Seen,
}

#[derive(Clone, Debug)]
pub struct BlockNode {
    state: Cell<TraversalState>,
    label: String,
}

impl BlockNode {
    pub fn new(l: &str) -> Self {
        Self { state: Cell::new(TraversalState::Start), label: l.to_string() }
    }
}

#[derive(Clone, Debug, Default)]
pub struct ControlFlowGraph {
    paths: HashMap<String, BTreeMap<(usize, String), BlockNode>>,
}

impl ControlFlowGraph {
    /// Adds an edge to our control flow graph.
    pub fn add_edge(&mut self, from: &str, to: &str, sort: usize) {
        self.paths
            .entry(from.to_string())
            .or_default()
            .insert((sort, to.to_string()), BlockNode::new(to));
    }
}

pub fn build_cfg(func: &Function) -> ControlFlowGraph {
    let mut cfg = ControlFlowGraph::default();

    'blocks: for (idx, block) in func.blocks.iter().enumerate() {
        let b_label = block.label.replace(':', "");

        let mut sort = 1;
        // TODO: only iter the branch instructions with labels
        for inst in &block.instructions {
            // TODO: can we make note of this for optimization...(if there are trailing
            // unreachable instructions)
            if inst.is_return() {
                continue 'blocks;
            }
            if let Some(label) = inst.uses_label() {
                cfg.add_edge(&b_label, label, sort);
                sort += 1;

                // Skip the implicit branch to the block below the current one
                // since we found an unconditional jump.
                //
                // TODO: can we make note of this for optimization...(if there are trailing
                // unreachable instructions)
                if inst.unconditional_jmp() {
                    continue 'blocks;
                }
            }
        }

        if let Some(next) = func.blocks.get(idx + 1) {
            let next_label = next.label.replace(':', "");
            cfg.add_edge(&b_label, &next_label, 0);
        }
    }

    cfg
}

fn traverse(val: &str, align: usize, cfg: &ControlFlowGraph, paths: &mut Vec<Vec<String>>) {
    let map = BTreeMap::default();
    let nodes = cfg.paths.get(val).unwrap_or(&map);

    if paths.is_empty() {
        paths.push(vec![val.to_string()]);
    } else {
        paths.last_mut().unwrap().push(val.to_string());
    }

    let last = paths.last().unwrap().clone();
    for (idx, ((_, s), node)) in nodes.iter().enumerate() {
        if idx > 0 {
            paths.push(last.clone())
        };

        if s == val || matches!(node.state.get(), TraversalState::Seen) {
            continue;
        }

        node.state.set(TraversalState::Seen);
        traverse(s, align + 5, cfg, paths);
        node.state.set(TraversalState::Start);
    }
}

#[derive(Debug)]
pub struct DominatorTree {
    dom_frontier_map: HashMap<String, HashSet<String>>,
    post_dom_frontier: HashMap<String, BTreeSet<String>>,
    post_dom: HashMap<String, BTreeSet<String>>,
    dom_succs_map: HashMap<String, BTreeSet<String>>,
    #[allow(unused)]
    dom_preds_map: HashMap<String, BTreeSet<String>>,
    cfg_succs_map: HashMap<String, BTreeSet<String>>,
    cfg_preds_map: HashMap<String, BTreeSet<String>>,
}

// TODO: Cleanup (see todo's above loops and such)
pub fn dominator_tree(cfg: &ControlFlowGraph, blocks: &mut [Block]) -> DominatorTree {
    let mut paths = vec![];
    traverse(".L_main", 0, cfg, &mut paths);

    // Build dominator tree
    let mut dom_map = HashMap::with_capacity(blocks.len());
    let blocks_label = blocks.iter().map(|b| b.label.replace(':', "")).collect::<Vec<_>>();
    for label in &blocks_label {
        let mut is_reachable = false;
        let mut set = blocks_label.iter().collect::<HashSet<_>>();
        for path in paths.iter().filter(|p| p.contains(label)) {
            is_reachable = true;

            let path_set = path.iter().take_while(|l| *l != label).collect::<HashSet<_>>();
            set = set.intersection(&path_set).copied().collect();
            if set.is_empty() {
                break;
            }
        }

        if is_reachable {
            set.insert(label);
            dom_map.insert(label.to_string(), set);
        }
    }

    // println!("dominator map:\n{:#?}", dom_map);

    // TODO: only one or none used figure it out!!!
    // Build dominance predecessor map (AKA find join points)
    let mut dom_preds_map = HashMap::with_capacity(blocks_label.len());
    let mut cfg_preds_map = HashMap::with_capacity(blocks_label.len());
    for label in &blocks_label {
        let mut pred = BTreeSet::new();
        let mut cfg_pred = BTreeSet::new();
        // For each index we find the label (this detects loops back to a node,
        // which is important when computing frontiers) we save the that index to check
        // what the previous label is in that path
        for (label_idxs, path) in paths.iter().map(|p| {
            (
                p.iter()
                    .enumerate()
                    .filter_map(|(i, l)| if l == label { Some(i) } else { None })
                    .collect::<Vec<usize>>(),
                p,
            )
        }) {
            for idx in label_idxs {
                let mut idx = idx;

                let mut cfg_first = true;
                while let Some(i) = idx.checked_sub(1) {
                    let prev = &path[i];
                    if cfg_first {
                        cfg_pred.insert(prev.to_string());
                        cfg_first = false;
                    }
                    if prev != label {
                        if dom_map.get(label).map_or(false, |dom_preds| dom_preds.contains(prev)) {
                            pred.insert(prev.to_string());
                            break;
                        } else {
                            idx -= 1;
                        }
                    } else {
                        break;
                    }
                }
            }
        }
        // If the set is empty there are no predecessors
        if !pred.is_empty() {
            dom_preds_map.insert(label.to_string(), pred);
        }
        if !cfg_pred.is_empty() {
            cfg_preds_map.insert(label.to_string(), cfg_pred);
        }
    }
    let mut dom_succs_map = HashMap::with_capacity(blocks_label.len());
    for (to, set) in &dom_preds_map {
        for from in set {
            dom_succs_map
                .entry(from.to_string())
                .or_insert_with(BTreeSet::new)
                .insert(to.to_string());
        }
    }
    let mut cfg_succs_map = HashMap::with_capacity(blocks_label.len());
    for (to, set) in &cfg_preds_map {
        for from in set {
            cfg_succs_map
                .entry(from.to_string())
                .or_insert_with(BTreeSet::new)
                .insert(to.to_string());
        }
    }

    let mut idom_map = HashMap::with_capacity(blocks_label.len());
    for label in &blocks_label {
        let mut labels = VecDeque::from([label]);
        while let Some(dfset) = labels.pop_front().and_then(|l| dom_preds_map.get(l)) {
            if dfset.len() == 1 {
                idom_map.insert(label.to_string(), (*dfset.iter().next().unwrap()).clone());
                break;
            }
            for df in dfset {
                labels.push_back(df);
            }
        }
    }

    // Keith Cooper/Linda Torczon EaC pg. 499 SSA dominance frontier algorithm
    let mut dom_frontier_map: HashMap<String, HashSet<String>> =
        HashMap::with_capacity(blocks_label.len());
    for label in &blocks_label {
        // Node must be a join point (have multiple preds)
        if let Some(preds) =
            cfg_preds_map.get(label).and_then(|p| if !p.is_empty() { Some(p) } else { None })
        {
            // For each previous node find a predecessor of `label` that also dominates `label
            for p in preds {
                let mut run = p;
                while Some(run) != idom_map.get(label) {
                    // TODO: I think this works because a dom frontier will only ever be a single
                    // node since no node with multiple predecessors can be in the `idom_map`.
                    //
                    // Second, for a join point j, each predecessor k of j must have j ∈ df(k),
                    // since k cannot dominate j if j has more than one predecessor. Finally, if j ∈
                    // df(k) for some predecessor k, then j must also be in df(l) for each l ∈
                    // Dom(k), unless l ∈ Dom( j)
                    dom_frontier_map.entry(run.to_string()).or_default().insert(label.to_string());
                    if let Some(idom) = idom_map.get(run) {
                        run = idom;
                    }
                }
            }
        }
    }

    let empty = BTreeSet::new();

    #[derive(Debug)]
    enum SiblingKind<'a> {
        Only(&'a String),
        Ignore(&'a String),
    }
    impl fmt::Display for SiblingKind<'_> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            match self {
                Self::Only(s) | Self::Ignore(s) => s.fmt(f),
            }
        }
    }
    impl SiblingKind<'_> {
        pub fn as_str(&self) -> &str {
            match self {
                Self::Only(s) | Self::Ignore(s) => s,
            }
        }
    }
    // This is just postdominators tree
    let mut post_dom = HashMap::<_, BTreeSet<_>>::with_capacity(blocks_label.len());
    for node in reverse_postoder(&cfg_succs_map) {
        let mut seen = HashSet::new();

        // Skip until we find a single common child...
        let s = node.to_string();
        let mut labels = VecDeque::from([SiblingKind::Ignore(&s)]);
        while let Some(n) = labels.pop_front() {
            if let Some(succs) = cfg_succs_map.get(n.as_str()) {
                // If the values has been seen
                if !seen.insert(succs) {
                    continue;
                }
                let kids: Vec<_> = if succs.len() > 1 {
                    // Jump as far down the graph as possible
                    succs.last().map(SiblingKind::Only).into_iter().collect()
                } else {
                    succs.iter().map(SiblingKind::Only).collect()
                };
                labels.extend(kids);
            }
            if let SiblingKind::Only(n) = n {
                post_dom.entry(node.to_string()).or_default().insert(n.to_string());
            }
        }
    }

    // This is control dependence
    let mut post_dom_frontier = HashMap::<_, BTreeSet<String>>::with_capacity(blocks_label.len());
    for node in reverse_postoder(&cfg_succs_map) {
        for c in cfg_succs_map.get(node).unwrap_or(&empty) {
            for m in post_dom_frontier.get(c).cloned().unwrap_or_default() {
                if !post_dom.get(node).map_or(false, |set| set.contains(&m)) {
                    post_dom_frontier.entry(m.to_string()).or_default().insert(node.to_string());
                }
            }
        }
        for m in cfg_preds_map.get(node).unwrap_or(&empty) {
            if !post_dom.get(node).map_or(false, |set| set.contains(m)) {
                post_dom_frontier.entry(m.to_string()).or_default().insert(node.to_string());
            }
        }
    }

    DominatorTree {
        dom_frontier_map,
        post_dom_frontier,
        post_dom,
        dom_succs_map,
        dom_preds_map,
        cfg_preds_map,
        cfg_succs_map,
    }
}

pub fn insert_phi_functions(
    blocks: &mut Vec<Block>,
    dom_front: &HashMap<String, HashSet<String>>,
) -> HashMap<String, HashSet<Operand>> {
    // All the registers that are used across blocks
    let mut globals = vec![];
    let mut blocks_map = HashMap::new();

    for blk in &*blocks {
        // This represents any redefinitions that are local to the current block
        let mut varkil = HashSet::new();
        for op in &blk.instructions {
            let (a, b) = op.operands();
            let dst = op.target_reg();
            if let Some(a @ Operand::Register(..)) = a {
                if !varkil.contains(&a) {
                    globals.push(a);
                }
            }
            if let Some(b @ Operand::Register(..)) = b {
                if !varkil.contains(&b) {
                    globals.push(b);
                }
            }
            if let Some(dst) = dst {
                varkil.insert(Operand::Register(*dst));
                blocks_map
                    .entry(Operand::Register(*dst))
                    .or_insert_with(HashSet::new)
                    .insert(blk.label.replace(':', ""));
            }
        }
    }

    let empty = HashSet::new();
    let mut phis: HashMap<_, HashSet<_>> = HashMap::new();
    for global_reg in &globals {
        let mut worklist =
            blocks_map.get(global_reg).unwrap_or(&empty).iter().collect::<VecDeque<_>>();
        // For every block that this variable is live in
        while let Some(blk) = worklist.pop_front() {
            // The dominance frontier (join point) is the block that needs
            // the 𝛟 added to it
            for d in dom_front.get(blk).unwrap_or(&empty) {
                // If we have done this before skip it
                if !phis.get(d).map_or(false, |set| set.contains(global_reg)) {
                    // insert phi func
                    phis.entry(d.to_string()).or_default().insert(global_reg.clone());
                    // This needs to be propagated back up the graph
                    worklist.push_back(d);
                }
            }
        }
    }

    for (label, set) in &phis {
        let instructions = blocks.iter_mut().find(|b| b.label.replace(':', "") == *label).unwrap();
        for reg in set {
            instructions
                .instructions
                .insert(0, Instruction::Phi(reg.copy_to_register(), BTreeSet::default(), None));
        }
    }
    phis
}

pub fn ssa_optimization(iloc: &mut IlocProgram) {
    for func in &mut iloc.functions {
        let mut cfg = build_cfg(func);

        let dtree = dominator_tree(&cfg, &mut func.blocks);

        let phis = insert_phi_functions(&mut func.blocks, &dtree.dom_frontier_map);

        let mut meta = HashMap::new();
        for (_blk_label, register_set) in phis {
            meta.extend(register_set.iter().map(|op| (op.clone(), RenameMeta::default())));
        }
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

        dead_code(func, &mut cfg, &dtree);

        // find_loops(func, &dtree);
    }
}

#[test]
fn ssa_cfg() {
    use std::fs;

    use crate::iloc::{make_blks, parse_text};

    let input = fs::read_to_string("input/check.il").unwrap();
    let iloc = parse_text(&input).unwrap();
    let blocks = make_blks(iloc, true);

    let cfg = build_cfg(&blocks.functions[0]);
    println!("{:?}", cfg);
    emit_cfg_viz(&cfg, "graphs/check.dot");
}

#[test]
fn ssa_cfg_while() {
    use std::fs;

    use crate::iloc::{make_blks, parse_text};

    let input = fs::read_to_string("input/turd.il").unwrap();
    let iloc = parse_text(&input).unwrap();
    let mut blocks = make_blks(iloc, true);

    let cfg = build_cfg(&blocks.functions[0]);
    // println!("{:?}", cfg);

    emit_cfg_viz(&cfg, "graphs/turd.dot");

    dominator_tree(&cfg, &mut blocks.functions[0].blocks);
}

#[test]
fn ssa_cfg_dumb() {
    use std::fs;

    use crate::iloc::{make_blks, parse_text};

    let input = fs::read_to_string("input/dumb.il").unwrap();
    let iloc = parse_text(&input).unwrap();
    let mut blocks = make_blks(iloc, true);
    ssa_optimization(&mut blocks);
}

#[test]
fn ssa_cfg_trap() {
    use std::fs;

    use crate::iloc::{make_blks, parse_text};

    let input = fs::read_to_string("input/turd.il").unwrap();
    let iloc = parse_text(&input).unwrap();
    let mut blocks = make_blks(iloc, true);

    let cfg = build_cfg(&blocks.functions[0]);
    let dom = dominator_tree(&cfg, &mut blocks.functions[0].blocks);

    println!("{:#?}", dom);
    // emit_cfg_viz(&cfg, "graphs/turd.dot");

    // dominator_tree(&cfg, &mut blocks.functions[0].blocks);
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
        seen.insert(n.clone());
        for BlockNode { label: e, .. } in map.values() {
            if !seen.contains(e) {
                writeln!(buf, "{} [ label = \"{}\", shape = square]", str_id(e), e).unwrap();
                seen.insert(e.clone());
            }
            writeln!(buf, "{} -> {}", str_id(n), str_id(e)).unwrap();
        }
    }
    writeln!(buf, "}}").unwrap();
    fs::write(file, buf).unwrap();
}

//
//
// SCRATCH IGNORE
//
//

// fn rename_values(
//     blks: &mut [Block],
//     blk_idx: usize,
//     meta: &mut HashMap<Operand, RenameMeta>,
//     cfg_succs: &HashMap<String, BTreeSet<String>>,
//     dom_succs: &HashMap<String, BTreeSet<String>>,
// ) {
//     let rng = phi_range(&blks[blk_idx].instructions);

//     for phi in &mut blks[blk_idx].instructions[rng.clone()] {
//         if let Instruction::Phi(r, _, dst) = phi {
//             new_name(r, dst, meta);
//         }
//     }

//     for op in &mut blks[blk_idx].instructions[rng.end..] {
//         let (a, b) = op.operands_mut();
//         if let Some((a, meta)) = a.and_then(|reg| {
//             let cpy = *reg;
//             Some((reg, meta.get(&Operand::Register(cpy))?))
//         }) {
//             rewrite_name(a, meta);
//         }
//         if let Some((b, meta)) = b.and_then(|reg| {
//             let cpy = *reg;
//             Some((reg, meta.get(&Operand::Register(cpy))?))
//         }) {
//             rewrite_name(b, meta);
//         }

//         let dst = op.target_reg_mut();
//         if let Some((dst, meta)) = dst.and_then(|d| {
//             let cpy = *d;
//             Some((d, meta.get_mut(&Operand::Register(cpy))?))
//         }) {
//             // This is `new_name` minus the set addition
//             let i = meta.counter;
//             meta.counter += 1;
//             meta.stack.push_back(i);

//             dst.as_phi(i);
//         }
//     }

//     let empty = BTreeSet::new();
//     let blk_label = blks[blk_idx].label.replace(':', "");

//     for blk in cfg_succs.get(&blk_label).unwrap_or(&empty) {
//         // println!("cfg succ {} {}", blk, blks[blk_idx].label);

//         // TODO: make block -> index map
//         let idx = blks.iter().position(|b| b.label.replace(':', "") == **blk).unwrap();
//         let rng = phi_range(&blks[idx].instructions);
//         for phi in &mut blks[idx].instructions[rng] {
//             if let Instruction::Phi(r, set, ..) = phi {
//                 let fill = meta
//                     .get(&Operand::Register(*r))
//                     .unwrap()
//                     .stack
//                     .back()
//                     .unwrap_or_else(|| panic!("{:?} {:?}", meta, r));
//                 set.insert(*fill);
//             }
//         }
//     }

//     // This is what drives the rename algorithm
//     for blk in dom_succs.get(&blk_label).unwrap_or(&empty) {
//         // TODO: make block -> index map
//         let idx = blks.iter().position(|b| b.label.replace(':', "") == **blk).unwrap();
//         rename_values(blks, idx, meta, cfg_succs, dom_succs);
//     }

//     for op in &blks[blk_idx].instructions {
//         if let Some(dst) = op.target_reg().map(Reg::as_register) {
//             if let Some(meta) = meta.get_mut(&Operand::Register(dst)) {
//                 meta.stack.pop_back();
//             }
//         }
//     }
// }
