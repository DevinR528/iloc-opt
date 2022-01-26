use std::collections::{HashMap, HashSet, VecDeque};

use crate::iloc::{Block, Function, Instruction};

#[derive(Clone, Debug, Default)]
pub struct CFGNode {
    pred: HashSet<Block>,
    succ: HashSet<Block>,
}

#[derive(Clone, Debug, Default)]
pub struct ControlFlowGraph {
    paths: HashMap<String, HashSet<String>>,
    entry: Option<String>,
}

impl ControlFlowGraph {
    pub fn new(blk: &Block) -> Self {
        let mut paths = HashMap::default();
        paths.insert(blk.label.clone(), HashSet::default());
        Self { paths, entry: Some(blk.label.clone()) }
    }

    /// Adds an edge to our control flow graph.
    pub fn add_edge(&mut self, from: &str, to: &str) {
        self.paths.entry(from.to_string()).or_default().insert(to.to_string());
    }
}

pub fn build_cfg(func: &Function) -> ControlFlowGraph {
    let entry = func.blocks.first().unwrap().clone();
    let mut cfg = ControlFlowGraph::default();

    'blocks: for (idx, block) in func.blocks.iter().enumerate() {
        let b_label = block.label.replace(':', "");

        for inst in &block.instructions {
            if let Some(label) = inst.uses_label() {
                cfg.add_edge(&b_label, label);

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

pub fn dominator_tree(cfg: &ControlFlowGraph) {
    let mut align = 0;
    let mut paths = vec![vec![".L_main".to_string()]];
    traverse(".L_main", align, cfg, &mut paths);
}

fn traverse(val: &str, align: usize, cfg: &ControlFlowGraph, paths: &mut Vec<Vec<String>>) {
    let set = HashSet::default();
    let nodes = cfg.paths.get(val).unwrap_or(&set).clone();

    if nodes.len() == 1 {
        paths.last_mut().unwrap().push(val.to_string());
    } else {
        let last = paths.last().unwrap().clone();
        for (idx, node) in nodes.iter().enumerate() {
            paths.push(last.clone());
            traverse(node, align + 5, cfg, paths);
        }
        println!("{}{}({})", " ".repeat(align), " ".repeat(7 - val.to_string().len()), val);
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
    println!("{:?}", cfg);
    emit_cfg_viz(&cfg, "while_array.dot");
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

    dominator_tree(&cfg);
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
    for (n, sets) in &cfg.paths {
        writeln!(buf, "{} [ label = \"{}\", shape = square]", str_id(n), n);
        seen.insert(n.clone());
        for e in sets {
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
