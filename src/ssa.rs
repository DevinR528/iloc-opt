use std::{
    borrow::Borrow,
    cell::Cell,
    collections::{
        hash_map::{Entry, RandomState},
        BTreeMap, BTreeSet, HashMap, HashSet, VecDeque,
    },
    fmt, hash,
    sync::Mutex,
};

use crate::iloc::{make_basic_blocks, Block, Function, IlocProgram, Instruction, Operand};

mod dbre;
mod dce;
mod fold;
mod lcm;
mod licm;

pub use dbre::{dom_val_num, RenameMeta};
use dce::dead_code;
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

/// This is parent -> children, where children is fall through then jump (ssa val numbering needs
/// this)
pub fn reverse_postorder<'a>(
    succs: &'a HashMap<OrdLabel, BTreeSet<OrdLabel>>,
    start: &'a OrdLabel,
) -> impl Iterator<Item = &'a OrdLabel> + 'a {
    let mut stack = VecDeque::from_iter([start]);
    let mut seen = HashSet::<_, RandomState>::from_iter([start]);
    std::iter::from_fn(move || {
        let val = stack.pop_front()?;
        if let Some(set) = succs.get(val) {
            for child in set {
                if seen.contains(child) {
                    continue;
                }
                stack.push_back(child)
            }
        }
        seen.insert(val);

        Some(val)
    })
}
/// Preorder is parent, left, right traversal of the cfg graph.
pub fn preorder<'a>(
    succs: &'a HashMap<OrdLabel, BTreeSet<OrdLabel>>,
    start: &'a OrdLabel,
) -> impl Iterator<Item = &'a OrdLabel> + 'a {
    let mut stack = VecDeque::from_iter([start]);
    let mut seen = HashSet::<_, RandomState>::from_iter([start]);
    std::iter::from_fn(move || {
        let val = stack.pop_front()?;
        if let Some(set) = succs.get(val) {
            for child in set {
                if seen.contains(child) {
                    continue;
                }
                stack.push_back(child)
            }
        }
        seen.insert(val);

        Some(val)
    })
}
/// Postorder is left child, right child, parent. This is the reverse graph
pub fn postorder<'a>(
    pred: &'a HashMap<OrdLabel, BTreeSet<OrdLabel>>,
    end: &'a OrdLabel,
) -> impl Iterator<Item = &'a OrdLabel> + 'a {
    let mut stack = VecDeque::from_iter([end]);
    let mut seen = HashSet::<_, RandomState>::from_iter([end]);
    std::iter::from_fn(move || {
        let val = stack.pop_front()?;
        if let Some(set) = pred.get(val) {
            for parent in set.iter().rev() {
                if seen.contains(parent) {
                    continue;
                }
                stack.push_back(parent)
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

static LABEL_MAP: std::lazy::SyncLazy<Mutex<HashMap<String, OrdLabel>>> =
    std::lazy::SyncLazy::new(|| Mutex::new(HashMap::new()));

#[derive(Clone)]
pub struct OrdLabel(isize, String);
impl OrdLabel {
    // Create a new `OrdLabel, removing the `:` and without the sorting filler in the front of the
    // label.
    fn new(label: &str) -> Self {
        Self(111, label.replace(':', ""))
    }
    fn new_add(sort: isize, label: &str) -> Self {
        match LABEL_MAP.lock().unwrap().entry(label.to_string()) {
            Entry::Occupied(o) => o.get().clone(),
            Entry::Vacant(v) => {
                let l = OrdLabel(sort, label.to_string());
                v.insert(l.clone());
                l
            }
        }
    }
    fn from_known(label: &str) -> Self {
        let jik = LABEL_MAP.lock().unwrap().clone();
        LABEL_MAP.lock().unwrap().get(label).unwrap_or_else(|| panic!("{label} {:?}", jik)).clone()
    }
    pub fn new_start(start: &str) -> Self {
        let l = Self(-1, format!(".F_{}", start));
        LABEL_MAP.lock().unwrap().entry(format!(".F_{}", start)).or_insert(l).clone()
    }
    fn as_str(&self) -> &str {
        self.1.trim_start_matches('!')
    }
}
impl fmt::Display for OrdLabel {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.as_str().fmt(f)
    }
}
impl fmt::Debug for OrdLabel {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // write!(f, "({} {})", self.0, self.1)
        self.as_str().fmt(f)
    }
}
impl PartialEq for OrdLabel {
    fn eq(&self, other: &Self) -> bool {
        self.as_str().eq(other.as_str())
    }
}
impl Eq for OrdLabel {}
impl hash::Hash for OrdLabel {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.1.hash(state);
    }
}
impl PartialOrd for OrdLabel {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match self.0.partial_cmp(&other.0) {
            Some(core::cmp::Ordering::Equal) => self.1.partial_cmp(&other.1),
            ord => ord,
        }
    }
}
impl Ord for OrdLabel {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match self.0.cmp(&other.0) {
            core::cmp::Ordering::Equal => self.1.cmp(&other.1),
            ord => ord,
        }
    }
}
impl PartialEq<str> for OrdLabel {
    fn eq(&self, other: &str) -> bool {
        self.as_str().eq(other)
    }
}
impl PartialEq<String> for OrdLabel {
    fn eq(&self, other: &String) -> bool {
        self.as_str().eq(other)
    }
}
impl Borrow<str> for OrdLabel {
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

#[derive(Clone, Debug, Default)]
pub struct ControlFlowGraph {
    paths: HashMap<String, BTreeMap<OrdLabel, BlockNode>>,
    end: Option<OrdLabel>,
}

impl ControlFlowGraph {
    /// Adds an edge to our control flow graph.
    pub fn add_edge(&mut self, from: &str, to: &str, sort: isize) {
        self.paths
            .entry(from.to_string())
            .or_default()
            .insert(OrdLabel::new_add(sort, to), BlockNode::new(to));
    }
}

pub fn build_cfg(func: &Function) -> ControlFlowGraph {
    let mut cfg = ControlFlowGraph::default();

    'block: for (idx, block) in func.blocks.iter().enumerate() {
        let b_label = block.label.replace(':', "");

        let mut sort = 1;
        let mut unreachable = false;
        // TODO: only iter the branch instructions with labels
        'inst: for inst in &block.instructions {
            // TODO: can we make note of this for optimization...(if there are trailing
            // unreachable instructions)
            if inst.is_return() {
                cfg.end = if idx == 0 {
                    Some(OrdLabel::new_add(0, &b_label))
                } else {
                    Some(OrdLabel::from_known(&b_label))
                };
                unreachable = true;
                continue 'inst;
            }

            if let Some(label) = inst.uses_label() {
                if unreachable {
                    let _save_the_label = OrdLabel::new_add(sort, label);
                } else {
                    cfg.add_edge(&b_label, label, sort);
                }

                sort += 1;

                // Skip the implicit branch to the block below the current one
                // since we found an unconditional jump.
                //
                // TODO: can we make note of this for optimization...(if there are trailing
                // unreachable instructions)
                if inst.unconditional_jmp() {
                    continue 'block;
                }
            }
        }

        if let Some(next) = func.blocks.get(idx + 1) {
            let next_label = next.label.replace(':', "");
            cfg.add_edge(&b_label, &next_label, 0);
        }
    }
    // println!("{:#?}", cfg);
    cfg
}

fn traverse(val: &OrdLabel, cfg: &ControlFlowGraph, paths: &mut Vec<Vec<OrdLabel>>) {
    let map = BTreeMap::default();
    let nodes = cfg.paths.get(val.as_str()).unwrap_or(&map);

    if paths.is_empty() {
        paths.push(vec![val.clone()]);
    } else {
        paths.last_mut().unwrap().push(val.clone());
    }

    let last = paths.last().unwrap().clone();
    for (idx, (s, node)) in nodes.iter().enumerate() {
        if idx > 0 {
            paths.push(last.clone())
        };

        if matches!(node.state.get(), TraversalState::Seen) {
            continue;
        }

        node.state.set(TraversalState::Seen);
        traverse(s, cfg, paths);
        node.state.set(TraversalState::Start);
    }
}

#[derive(Debug)]
pub struct DominatorTree {
    pub dom_frontier_map: HashMap<OrdLabel, BTreeSet<OrdLabel>>,
    post_dom_frontier: HashMap<OrdLabel, BTreeSet<OrdLabel>>,
    post_dom: HashMap<OrdLabel, BTreeSet<OrdLabel>>,
    dom_map: HashMap<OrdLabel, BTreeSet<OrdLabel>>,
    dom_tree: HashMap<OrdLabel, BTreeSet<OrdLabel>>,
    #[allow(unused)]
    dom_preds_map: HashMap<OrdLabel, BTreeSet<OrdLabel>>,
    cfg_succs_map: HashMap<OrdLabel, BTreeSet<OrdLabel>>,
    cfg_preds_map: HashMap<OrdLabel, BTreeSet<OrdLabel>>,
}

// TODO: Cleanup (see todo's above loops and such)
pub fn dominator_tree(
    cfg: &ControlFlowGraph,
    blocks: &mut [Block],
    start: &OrdLabel,
) -> DominatorTree {
    let mut paths = vec![];
    traverse(start, cfg, &mut paths);

    // Build dominator tree
    let mut dom_map = HashMap::with_capacity(blocks.len());
    let blocks_label =
        blocks.iter().map(|b| OrdLabel::from_known(&b.label.replace(':', ""))).collect::<Vec<_>>();

    for node in &blocks_label {
        let mut is_reachable = false;
        let mut set = blocks_label.iter().collect::<BTreeSet<_>>();
        for path in paths.iter().filter(|p| p.contains(node)) {
            is_reachable = true;

            let path_set = path.iter().take_while(|l| *l != node).collect::<BTreeSet<_>>();
            set = set.intersection(&path_set).copied().collect();
            if set.is_empty() {
                break;
            }
        }

        if is_reachable {
            // set.insert(node);
            dom_map.insert(node.clone(), set.into_iter().cloned().collect());
        }
    }

    // println!("dominator map:\n{:#?}", dom_map);

    // TODO: only one or none used figure it out!!!
    // Build dominance predecessor map (AKA find join points)
    let mut dom_preds_map = HashMap::with_capacity(blocks_label.len());
    let mut cfg_preds_map = HashMap::with_capacity(blocks_label.len());
    for node in &blocks_label {
        let mut pred = BTreeSet::new();
        let mut cfg_pred = BTreeSet::new();
        // For each index we find the label (this detects loops back to a node,
        // which is important when computing frontiers) we save that the index to check
        // what the previous label is in that path
        for (label_idxs, path) in paths.iter().map(|p| {
            (
                p.iter()
                    .enumerate()
                    .filter_map(|(i, l)| if l == node { Some(i) } else { None })
                    .collect::<Vec<usize>>(),
                p,
            )
        }) {
            for mut idx in label_idxs {
                let mut cfg_first = true;
                while let Some(i) = idx.checked_sub(1) {
                    let prev = &path[i];
                    if cfg_first {
                        cfg_pred.insert(prev.clone());
                        cfg_first = false;
                    }
                    if prev != node {
                        if dom_map.get(node).map_or(false, |dom: &BTreeSet<_>| dom.contains(prev)) {
                            pred.insert(prev.clone());
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
            dom_preds_map.insert(node.clone(), pred);
        }
        if !cfg_pred.is_empty() {
            cfg_preds_map.insert(node.clone(), cfg_pred);
        }
    }
    let mut dom_tree = HashMap::with_capacity(blocks_label.len());
    for (to, set) in &dom_preds_map {
        for from in set {
            dom_tree.entry(from.clone()).or_insert_with(BTreeSet::new).insert(to.clone());
        }
    }
    let mut cfg_succs_map = HashMap::with_capacity(blocks_label.len());
    for (to, set) in &cfg_preds_map {
        for from in set {
            cfg_succs_map.entry(from.clone()).or_insert_with(BTreeSet::new).insert(to.clone());
        }
    }

    let mut idom_map = HashMap::with_capacity(blocks_label.len());
    for node in &blocks_label {
        let mut labels = VecDeque::from([node]);
        while let Some(dfset) = labels.pop_front().and_then(|l| dom_preds_map.get(l)) {
            if dfset.len() == 1 {
                idom_map.insert(node, (*dfset.iter().next().unwrap()).clone());
                break;
            }
            labels.extend(dfset);
        }
    }

    // Keith Cooper/Linda Torczon EaC pg. 499 SSA dominance frontier algorithm
    //
    // This is a mapping of node -> descendent in graph that is join point for this node
    // (anytime the graph make the lower half of a diamond)
    let mut dom_frontier_map: HashMap<OrdLabel, BTreeSet<OrdLabel>> =
        HashMap::with_capacity(blocks_label.len());
    for node in &blocks_label {
        // Node must be a join point (have multiple preds)

        // For each previous node find a predecessor of `label` that also dominates `label
        for p in cfg_preds_map.get(node).unwrap_or(&BTreeSet::new()) {
            let mut run = p;
            while Some(run) != idom_map.get(node) {
                // Second, for a join point j, each predecessor k of j must have j ∈ df(k),
                // since k cannot dominate j if j has more than one predecessor. Finally, if j ∈
                // df(k) for some predecessor k, then j must also be in df(l) for each l ∈
                // Dom(k), unless l ∈ Dom( j)
                dom_frontier_map.entry(run.clone()).or_default().insert(node.clone());
                if let Some(idom) = idom_map.get(run) {
                    run = idom;
                }
            }
        }
    }

    // This is just postdominators tree
    let mut post_dom = HashMap::<_, BTreeSet<_>>::with_capacity(blocks_label.len());
    for node in postorder(&cfg_preds_map, cfg.end.as_ref().unwrap()) {
        let mut is_reachable = false;
        let mut set = blocks_label.iter().cloned().collect::<BTreeSet<_>>();
        for path in paths.iter().filter(|p| p.contains(node)) {
            is_reachable = true;
            let path_set =
                // Skip all before and the block itself, since we only want successors
                path.iter().skip_while(|l| *l != node).skip(1).cloned().collect::<BTreeSet<_>>();
            set = set.intersection(&path_set).cloned().collect();
            if set.is_empty() {
                break;
            }
        }
        if is_reachable && !set.is_empty() {
            // set.insert(label.clone());
            post_dom.insert(node.clone(), set);
        }
    }
    let empty = BTreeSet::new();
    let mut post_dom_tree = HashMap::<_, BTreeSet<_>>::with_capacity(blocks_label.len());
    for (f, pd) in &post_dom {
        let mut succs: VecDeque<_> = cfg_succs_map.get(f).unwrap_or(&empty).iter().collect();
        while let Some(n) = succs.pop_front() {
            if pd.contains(n) {
                post_dom_tree.entry(n.clone()).or_default().insert(f.clone());
                break;
            }
            succs.extend(cfg_succs_map.get(n).into_iter().flatten())
        }
    }
    let mut post_dom_tree_preds = HashMap::<_, BTreeSet<_>>::with_capacity(blocks_label.len());
    for (f, pd) in &post_dom_tree {
        for t in pd {
            post_dom_tree_preds.entry(t.clone()).or_default().insert(f.clone());
        }
    }
    let mut post_idom_map = HashMap::with_capacity(blocks_label.len());
    for node in reverse_postorder(&post_dom_tree, cfg.end.as_ref().unwrap()) {
        let mut labels = VecDeque::from([node]);
        while let Some(pdfset) = labels.pop_front().and_then(|l| post_dom_tree_preds.get(l)) {
            if pdfset.len() == 1 {
                post_idom_map.insert(node.clone(), (*pdfset.first().unwrap()).clone());
                break;
            }
            labels.extend(pdfset);
        }
    }

    // This is control dependence
    let mut post_dom_frontier = HashMap::<_, BTreeSet<OrdLabel>>::with_capacity(blocks_label.len());
    for node in postorder(&post_dom_tree, cfg.end.as_ref().unwrap()) {
        // This is post dominator frontier
        // This includes 1 -> 2 __and__ 1 -> 5 (the graph from his notes
        // and similar to https://pages.cs.wisc.edu/~fischer/cs701.f08/lectures/Lecture19.4up.pdf slide 6)
        //
        // for p in cfg_succs_map.get(node).unwrap_or(&BTreeSet::new()) {
        //     let mut run = p;
        //     while Some(run) != post_idom_map.get(node) {
        //         post_dom_frontier.entry(run.clone()).or_default().insert(node.clone());
        //         if let Some(idom) = post_idom_map.get(run) {
        //             run = idom;
        //         }
        //     }
        // }

        // Carr's isn't the same as post dominator frontier...
        // It misses 1 -> 5 (see above)
        //
        for c in cfg_succs_map.get(node).unwrap_or(&empty) {
            for m in post_dom_frontier.get(c).cloned().unwrap_or_default() {
                if !post_dom_tree.get(node).map_or(false, |set| set.contains(&m)) {
                    post_dom_frontier.entry(node.clone()).or_default().insert(m.clone());
                }
            }
        }
        for m in cfg_preds_map.get(node).unwrap_or(&empty) {
            if !post_dom_tree.get(node).map_or(false, |set| set.contains(m)) {
                post_dom_frontier.entry(node.clone()).or_default().insert(m.clone());
            }
        }
    }

    // println!("{:#?}", cfg_succs_map);

    DominatorTree {
        dom_frontier_map,
        post_dom_frontier,
        post_dom,
        dom_map,
        dom_tree,
        dom_preds_map,
        cfg_preds_map,
        cfg_succs_map,
    }
}

pub fn insert_phi_functions(
    blocks: &mut Vec<Block>,
    dom_front: &HashMap<OrdLabel, BTreeSet<OrdLabel>>,
) -> HashMap<OrdLabel, HashSet<Operand>> {
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
                    .insert(OrdLabel::new(&blk.label));
            }
        }
    }

    let empty = HashSet::new();
    let empty_set = BTreeSet::new();
    let mut phis: HashMap<_, HashSet<_>> = HashMap::new();
    for global_reg in &globals {
        let mut worklist =
            blocks_map.get(global_reg).unwrap_or(&empty).iter().collect::<VecDeque<_>>();
        // For every block that this variable is live in
        while let Some(blk) = worklist.pop_front() {
            // The dominance frontier (join point) is the block that needs
            // the 𝛟 added to it
            for d in dom_front.get(blk).unwrap_or(&empty_set) {
                // println!("{} -> {}", blk.as_str(), d.as_str());

                // If we have seen this register or it isn't in the current block we are checking
                // skip it
                if !phis.get(d).map_or(false, |set| set.contains(global_reg))
                    && blocks_map.get(global_reg).map_or(false, |blk_set| blk_set.contains(d))
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
        let blk = blocks.iter_mut().find(|b| b.label.starts_with(label.as_str())).unwrap();
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
        let mut cfg = build_cfg(func);

        let dtree = dominator_tree(&cfg, &mut func.blocks, &OrdLabel::new_start(&func.label));

        println!("{:#?}", dtree);

        let phis = insert_phi_functions(&mut func.blocks, &dtree.dom_frontier_map);

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

        dead_code(func, &mut cfg, &dtree);

        // find_loops(func, &dtree);
    }
}

#[test]
fn ssa_cfg() {
    use std::fs;

    use crate::iloc::{make_blks, parse_text};

    let input = fs::read_to_string("input/arrayparam.il").unwrap();
    let iloc = parse_text(&input).unwrap();
    let blocks = make_basic_blocks(&make_blks(iloc));

    let cfg = build_cfg(&blocks.functions[1]);
    println!("{:?}", cfg);
    emit_cfg_viz(&cfg, "graphs/arrayparam.dot");
}

#[test]
fn ssa_cfg_while() {
    use std::fs;

    use crate::iloc::{make_blks, parse_text};

    let input = fs::read_to_string("input/turd.il").unwrap();
    let iloc = parse_text(&input).unwrap();
    let mut blocks = make_basic_blocks(&make_blks(iloc));

    let cfg = build_cfg(&blocks.functions[0]);
    // println!("{:?}", cfg);

    emit_cfg_viz(&cfg, "graphs/turd.dot");

    let name = OrdLabel::new_start(&blocks.functions[0].label);
    dominator_tree(&cfg, &mut blocks.functions[0].blocks, &name);
}

#[test]
fn ssa_cfg_dumb() {
    use std::fs;

    use crate::iloc::{make_blks, parse_text};

    let input = fs::read_to_string("input/dumb.il").unwrap();
    let iloc = parse_text(&input).unwrap();
    let mut blocks = make_basic_blocks(&make_blks(iloc));
    ssa_optimization(&mut blocks);
}

#[test]
fn ssa_cfg_trap() {
    use std::fs;

    use crate::iloc::{make_blks, parse_text};

    let input = fs::read_to_string("input/turd.il").unwrap();
    let iloc = parse_text(&input).unwrap();
    let mut blocks = make_basic_blocks(&make_blks(iloc));

    let cfg = build_cfg(&blocks.functions[0]);
    let name = OrdLabel::new_start(&blocks.functions[0].label);
    let dom = dominator_tree(&cfg, &mut blocks.functions[0].blocks, &name);

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
