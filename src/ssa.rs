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

    /// Adds an edge to our control flow graph and returns if the graph was changed
    /// which helps us know if we need to keep iterating.
    ///
    /// Returns `false` when we have seen this node and true when it updates the graph.
    pub fn add_edge(&mut self, blk: &str) -> bool {
        let blk = blk.replace(':', "");
        let changed = if let Some(prev) = self.entry.take() {
            println!("blk = {} prev = {}", blk, prev);

            self.paths.entry(prev).or_default().insert(blk.to_string())
        } else {
            self.paths.insert(blk.to_string(), HashSet::default()).is_none()
        };

        self.entry = Some(blk);
        changed
    }
}

pub fn build_cfg(func: &Function) -> ControlFlowGraph {
    let entry = func.blocks.first().unwrap().clone();
    let mut cfg = ControlFlowGraph::default();

    let mut to_uncond = HashSet::new();
    let mut from_uncond = HashSet::new();
    let mut work_stack = VecDeque::new();
    for block in &func.blocks {
        work_stack.push_back(block);
        while let Some(curr_blk) = work_stack.pop_front() {
            if !cfg.add_edge(&curr_blk.label) {
                println!("cheat {:?}", cfg.entry);
                continue;
            }

            for inst in &curr_blk.instructions {
                if let Some(label) = inst.uses_label() {
                    if inst.unconditional_jmp() {
                        cfg.paths
                            .entry(curr_blk.label.replace(':', ""))
                            .or_default()
                            .insert(label.to_string());
                        from_uncond.insert(curr_blk.label.replace(':', ""));
                        to_uncond.insert(label);
                        continue;
                    }

                    work_stack.push_back(
                        func.blocks
                            .iter()
                            .find(|b| b.label.replace(':', "") == label)
                            .unwrap_or_else(|| panic!("{:#?}", func.blocks)),
                    );
                }
            }
        }

        println!("unc {:?} {:?}", from_uncond, to_uncond);
        println!("work {:?}", block.label);

        if from_uncond.contains(cfg.entry.as_deref().unwrap_or("")) {
            from_uncond.remove(cfg.entry.as_deref().unwrap_or(""));
            println!("taken {:?}", cfg.entry.take());
        } else {
            cfg.entry = Some(block.label.replace(':', ""));
        }
    }

    cfg
}

pub fn dominator_tree(cfg: ControlFlowGraph) {}

#[test]
fn ssa_cfg() {
    use std::fs;

    use crate::iloc::{make_blks, parse_text};

    let input = fs::read_to_string("input/check.il").unwrap();
    let mut iloc = parse_text(&input).unwrap();
    let mut blocks = make_blks(iloc);

    let cfg = build_cfg(&blocks.functions[0]);
    println!("{:?}", cfg);
    emit_cfg_viz(cfg, "check.dot");
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
    emit_cfg_viz(cfg, "while_array.dot");
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
    emit_cfg_viz(cfg, "dumb.dot");
}

fn emit_cfg_viz(cfg: ControlFlowGraph, file: &str) {
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
    for (n, sets) in cfg.paths {
        writeln!(buf, "{} [ label = \"{}\", shape = square]", str_id(&n), n);
        seen.insert(n.clone());
        for e in sets {
            if !seen.contains(&e) {
                writeln!(buf, "{} [ label = \"{}\", shape = square]", str_id(&e), e);
                seen.insert(e.clone());
            }
            writeln!(buf, "{} -> {}", str_id(&n), str_id(&e));
        }
    }
    writeln!(buf, "}}");
    fs::write(file, buf).unwrap();
}
