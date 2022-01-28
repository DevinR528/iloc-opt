use std::{
    cell::Cell,
    collections::{HashMap, HashSet, VecDeque},
};

use crate::iloc::{Block, Function, Instruction};

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

pub fn dominator_tree(cfg: &ControlFlowGraph, blocks: &[Block]) {
    let mut align = 0;

    let mut paths = vec![];
    traverse(".L_main", align, cfg, &mut paths);

    println!("{:#?}", paths);

    // Build dominator tree
    let mut dom_map = HashMap::with_capacity(blocks.len());
    let blocks = blocks.iter().map(|b| b.label.replace(':', "")).collect::<Vec<_>>();
    for label in &blocks {
        let mut is_reachable = false;
        let mut set = blocks.iter().collect::<HashSet<_>>();
        for path in paths.iter().filter(|p| p.contains(label)) {
            is_reachable = true;

            let path_set = path.iter().take_while(|l| *l != label).collect::<HashSet<_>>();
            set = set.intersection(&path_set).copied().collect();
            if set.is_empty() {
                break;
            }
        }

        if is_reachable {
            dom_map.insert(label.to_string(), set);
        }
    }

    println!("dominator map:\n{:#?}", dom_map);

    // Build dominance frontier map
    let mut dom_frontier_map = HashMap::with_capacity(blocks.len());
    for label in &blocks {
        let mut set = HashSet::new();
        for (label_idx, path) in
            paths.iter().filter_map(|p| Some((p.iter().position(|l| l == label)?, p)))
        {
            if let Some(idx) = label_idx.checked_sub(1) {
                set.insert(&path[idx]);
            }
        }

        // If the set is empty there are no predecessors
        if !set.is_empty() {
            dom_frontier_map.insert(label.to_string(), set);
        }
    }

    println!("frontier map:\n{:#?}", dom_frontier_map);
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

    dominator_tree(&cfg, &blocks.functions[0].blocks);
}

#[test]
fn ssa_cfg_dumb() {
    use std::fs;

    use crate::iloc::{make_blks, parse_text};

    let input = fs::read_to_string("input/dumb.il").unwrap();
    let mut iloc = parse_text(&input).unwrap();
    let mut blocks = make_blks(iloc);

    let cfg = build_cfg(&blocks.functions[0]);

    println!("{:?}", cfg);
    emit_cfg_viz(&cfg, "dumb.dot");

    dominator_tree(&cfg, &blocks.functions[0].blocks);
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

    dominator_tree(&cfg, &blocks.functions[0].blocks);
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
