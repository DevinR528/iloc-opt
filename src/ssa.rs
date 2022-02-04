use std::{
    cell::Cell,
    collections::{HashMap, HashSet, VecDeque},
    ops::Range,
};

use crate::iloc::{Block, Function, Instruction, Operand, Reg};

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
    paths: HashMap<String, HashMap<String, BlockNode>>,
    entry: Option<String>,
}

impl ControlFlowGraph {
    pub fn new(blk: &Block) -> Self {
        let mut paths = HashMap::default();
        paths.insert(blk.label.clone(), HashMap::default());
        Self { paths, entry: Some(blk.label.clone()) }
    }

    /// Adds an edge to our control flow graph.
    pub fn add_edge(&mut self, from: &str, to: &str) {
        self.paths.entry(from.to_string()).or_default().insert(to.to_string(), BlockNode::new(to));
    }
}

pub fn build_cfg(func: &Function) -> ControlFlowGraph {
    let entry = func.blocks.first().unwrap().clone();
    let mut cfg = ControlFlowGraph::default();

    'blocks: for (idx, block) in func.blocks.iter().enumerate() {
        let b_label = block.label.replace(':', "");

        // TODO: only iter the branch instructions with labels
        for inst in &block.instructions {
            // TODO: can we make note of this for optimization...(if there are trailing
            // unreachable instructions)
            if inst.is_return() {
                continue 'blocks;
            }
            if let Some(label) = inst.uses_label() {
                cfg.add_edge(&b_label, label);

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
            cfg.add_edge(&b_label, &next_label);
        }
    }

    cfg
}

pub struct DominatorTree {
    dom_map: HashMap<String, HashSet<String>>,
    dom_frontier_map: HashMap<String, HashSet<String>>,
}

fn traverse(val: &str, align: usize, cfg: &ControlFlowGraph, paths: &mut Vec<Vec<String>>) {
    let map = HashMap::default();
    let nodes = cfg.paths.get(val).unwrap_or(&map);

    if paths.is_empty() {
        paths.push(vec![val.to_string()]);
    } else {
        paths.last_mut().unwrap().push(val.to_string());
    }

    let last = paths.last().unwrap().clone();
    for (idx, (s, node)) in nodes.iter().enumerate() {
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

// TODO: Cleanup (see todo's above loops and such)
pub fn dominator_tree(cfg: &ControlFlowGraph, blocks: &mut Vec<Block>) {
    let mut align = 0;

    let mut paths = vec![];
    traverse(".L_main", align, cfg, &mut paths);

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
    let mut dom_succs_map = HashMap::with_capacity(blocks_label.len());
    let mut dom_preds_map = HashMap::with_capacity(blocks_label.len());
    for label in &blocks_label {
        let mut succ = HashSet::new();
        let mut pred = HashSet::new();
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
                if let Some(idx) = idx.checked_sub(1) {
                    pred.insert(&path[idx]);
                }
                if let Some(l) = path.get(idx + 1) {
                    succ.insert(l);
                }
            }
        }

        // If the set is empty there are no predecessors
        if !pred.is_empty() {
            dom_preds_map.insert(label.to_string(), pred);
        }
        if !succ.is_empty() {
            dom_succs_map.insert(label.to_string(), succ);
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

    let mut idom_succs_map = HashMap::with_capacity(blocks_label.len());
    for (to, from) in &idom_map {
        idom_succs_map.entry(from.to_string()).or_insert_with(HashSet::new).insert(to);
    }
    // println!("succs map:\n{:#?}", dom_succs_map);
    // println!("idom map:\n{:#?}", idom_succs_map);

    // Keith Cooper/Linda Torczon EaC pg. 499 SSA dominance frontier algorithm
    let mut fdom_map: HashMap<String, HashSet<String>> = HashMap::with_capacity(blocks_label.len());
    for label in &blocks_label {
        // Node must be a join point (have multiple preds)
        if let Some(preds) =
            dom_preds_map.get(label).and_then(|p| if p.len() > 1 { Some(p) } else { None })
        {
            // For each previous node find a predecessor of `label` that also dominates `label
            for p in preds {
                let mut run = *p;
                while Some(run) != idom_map.get(label) {
                    // TODO: I think this works because a dom frontier will only ever be a single
                    // node since no node with multiple predecessors can be in the `idom_map`.
                    //
                    // Second, for a join point j, each predecessor k of j must have j ∈ df(k),
                    // since k cannot dominate j if j has ore than one predecessor. Finally, if j ∈
                    // df(k) for some predecessor k, then j must also be in df(l) for each l ∈
                    // Dom(k), unless l ∈ Dom( j)
                    fdom_map.entry(run.to_string()).or_default().insert(label.to_string());
                    if let Some(idom) = idom_map.get(run) {
                        run = idom;
                    }
                }
            }
        }
    }

    // println!("frontier map:\n{:#?}", fdom_map);

    println!("{:#?}\n", blocks);

    insert_phi_functions(blocks, &fdom_map);
    let mut meta = HashMap::new();
    rename_values(blocks, 0, &mut meta, &dom_succs_map, &idom_succs_map);

    println!("{:#?}", blocks);
}

#[derive(Debug, Default)]
pub struct RenameMeta {
    counter: usize,
    stack: VecDeque<Operand>,
}

fn new_name(reg: &mut Reg, meta: &mut HashMap<Operand, RenameMeta>) {
    let m = meta.entry(Operand::Register(*reg)).or_default();
    let i = m.counter;

    m.counter += 1;

    m.stack.push_back(Operand::Register(Reg::Var(i)));
    *reg = Reg::Var(i);
}

fn rewrite_name(reg: &mut Reg, meta: &mut HashMap<Operand, RenameMeta>) {
    let m = meta.entry(Operand::Register(*reg)).or_default();
    let new = m.stack.back().unwrap_or_else(|| panic!("{:?} {:?}", m, reg)).copy_to_register();
    *reg = new;
}
fn phi_range(insts: &[Instruction]) -> Range<usize> {
    0..insts.iter().take_while(|i| i.is_phi()).count()
}

pub fn rename_values(
    blks: &mut [Block],
    blk_idx: usize,
    meta: &mut HashMap<Operand, RenameMeta>,
    succs: &HashMap<String, HashSet<&String>>,
    dom_succs: &HashMap<String, HashSet<&String>>,
) {
    let rng = phi_range(&blks[blk_idx].instructions);

    for phi in &mut blks[blk_idx].instructions[rng.clone()] {
        if let Instruction::Phi(r, ..) = phi {
            new_name(r, meta);
        }
    }

    for op in &mut blks[blk_idx].instructions[rng.end..] {
        let (a, b) = op.operands_mut();
        if let Some(a) = a {
            rewrite_name(a, meta);
        }
        if let Some(b) = b {
            rewrite_name(b, meta);
        }

        let dst = op.target_reg_mut();
        if let Some(dst) = dst {
            new_name(dst, meta);
        }
    }

    let empty = HashSet::new();
    let blk_label = blks[blk_idx].label.replace(':', "");

    for blk in succs.get(&blk_label).unwrap_or(&empty) {
        // TODO: make block -> index map
        let idx = blks.iter().position(|b| b.label.replace(':', "") == **blk).unwrap();
        let rng = phi_range(&blks[idx].instructions);

        for phi in &mut blks[idx].instructions[rng] {
            if let Instruction::Phi(r, set) = phi {
                set.insert(blk.to_string());
            }
        }
    }

    // This is what drives the rename algorithm
    for blk in dom_succs.get(&blk_label).unwrap_or(&empty) {
        // TODO: make block -> index map
        let idx = blks.iter().position(|b| b.label.replace(':', "") == **blk).unwrap();
        rename_values(blks, idx, meta, succs, dom_succs);
    }

    for op in &blks[blk_idx].instructions {
        let dst = if let Some(d) = op.target_reg() {
            d
        } else {
            continue;
        };
        if let Some(stack) = meta.get_mut(&Operand::Register(*dst)) {
            stack.stack.pop_back();
        }
    }
}

pub fn insert_phi_functions(blocks: &mut Vec<Block>, dom_front: &HashMap<String, HashSet<String>>)
// -> (HashMap<String, HashSet<Operand>>, HashMap<Operand, HashSet<String>>)
{
    let mut globals = vec![];
    let mut blocks_map = HashMap::new();

    for blk in &*blocks {
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

    // println!("globals: {:#?}", globals);
    // println!("reg -> block: {:#?}", blocks_map);

    let empty = HashSet::new();
    let mut phis: HashMap<_, HashSet<_>> = HashMap::new();
    for x in &globals {
        let mut worklist = blocks_map.get(x).unwrap_or(&empty).iter().collect::<VecDeque<_>>();
        // For every block that this variable is live in
        while let Some(blk) = worklist.pop_front() {
            // The dominance frontier (join point) is the block that needs
            // the 𝛟 added to it
            for d in dom_front.get(blk).unwrap_or(&empty) {
                // If we have done this before skip it
                if !phis.get(d).map_or(false, |set| set.contains(x)) {
                    // insert phi func
                    phis.entry(d.to_string()).or_default().insert(x.clone());
                    // This needs to be propagated back up the graph
                    worklist.push_back(d);
                }
            }
        }
    }

    // println!("phis: {:#?}", phis);

    // let mut otherway = HashMap::with_capacity(phis.len());
    // for (label, set) in &phis {
    //     for reg in set {
    //         otherway.entry(reg.clone()).or_insert_with(HashSet::new).insert(label.to_string());
    //     }
    // }
    for (label, set) in &phis {
        let instructions = blocks.iter_mut().find(|b| b.label.replace(':', "") == *label).unwrap();
        for reg in set {
            instructions
                .instructions
                .insert(0, Instruction::Phi(reg.copy_to_register(), HashSet::default()));
        }
    }
}

#[test]
fn ssa_cfg() {
    use std::fs;

    use crate::iloc::{make_blks, parse_text};

    let input = fs::read_to_string("input/check.il").unwrap();
    let mut iloc = parse_text(&input).unwrap();
    let mut blocks = make_blks(iloc);

    let cfg = build_cfg(&blocks.functions[0]);
    println!("{:?}", cfg);
    emit_cfg_viz(&cfg, "check.dot");
}

#[test]
fn ssa_cfg_while() {
    use std::fs;

    use crate::iloc::{make_blks, parse_text};

    let input = fs::read_to_string("input/while_array.il").unwrap();
    let mut iloc = parse_text(&input).unwrap();
    let mut blocks = make_blks(iloc);

    let cfg = build_cfg(&blocks.functions[0]);
    // println!("{:?}", cfg);

    emit_cfg_viz(&cfg, "while_array.dot");

    dominator_tree(&cfg, &mut blocks.functions[0].blocks);
}

#[test]
fn ssa_cfg_dumb() {
    use std::fs;

    use crate::iloc::{make_blks, parse_text};

    let input = fs::read_to_string("input/dumb.il").unwrap();
    let mut iloc = parse_text(&input).unwrap();
    let mut blocks = make_blks(iloc);

    let cfg = build_cfg(&blocks.functions[0]);

    // println!("{:?}", cfg);
    emit_cfg_viz(&cfg, "dumb.dot");

    for func in &mut blocks.functions {
        dominator_tree(&cfg, &mut func.blocks);
    }
}

#[test]
fn ssa_cfg_trap() {
    use std::fs;

    use crate::iloc::{make_blks, parse_text};

    let input = fs::read_to_string("input/trap.il").unwrap();
    let mut iloc = parse_text(&input).unwrap();
    let mut blocks = make_blks(iloc);

    let cfg = build_cfg(&blocks.functions[0]);

    println!("{:?}", cfg);
    emit_cfg_viz(&cfg, "trap.dot");

    dominator_tree(&cfg, &mut blocks.functions[0].blocks);
}

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
    writeln!(buf, "digraph cfg {{");
    for (n, map) in &cfg.paths {
        writeln!(buf, "{} [ label = \"{}\", shape = square]", str_id(n), n);
        seen.insert(n.clone());
        for BlockNode { label: e, .. } in map.values() {
            if !seen.contains(e) {
                writeln!(buf, "{} [ label = \"{}\", shape = square]", str_id(e), e);
                seen.insert(e.clone());
            }
            writeln!(buf, "{} -> {}", str_id(n), str_id(e));
        }
    }
    writeln!(buf, "}}");
    fs::write(file, buf).unwrap();
}
