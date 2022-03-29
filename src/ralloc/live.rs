use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque},
    fmt,
    ops::{AddAssign, Range},
};

use crate::{
    iloc::{Block, Function, Instruction, Operand, Reg},
    lcm::{print_maps, LoopAnalysis},
    ssa::{postorder, reverse_postorder, DominatorTree, OrdLabel},
};

pub const K_DEGREE: usize = 4;

#[derive(Debug)]
pub struct RegisterRange {
    reg: Reg,
    range: Range<usize>,
    count: usize,
}
impl RegisterRange {
    pub fn new(reg: Reg, start: usize) -> Self {
        Self { reg, range: start..start, count: 0 }
    }

    pub fn add_range(&mut self, rng: usize, block_idx: usize, inst_idx: usize) {
        self.count += 1;
        if rng > self.range.end {
            self.range.end = rng;
        } else if rng < self.range.start {
            self.range.start = rng;
        } else {
            println!("within range: {:?}", self);
        }
    }
}

fn find_cheap_spill(
    graph: &mut VecDeque<(Reg, BTreeSet<Reg>)>,
    blocks: &[Block],
    defs: &BTreeMap<Reg, (usize, usize)>,
    uses: &BTreeMap<Reg, Vec<(&OrdLabel, usize, usize)>>,
    loop_map: &LoopAnalysis,
) -> (Reg, BTreeSet<Reg>) {
    let mut best = 10000000000_isize;
    let mut best_idx = 0;

    for (idx, (r, set)) in graph.iter().enumerate() {
        let degree = set.len() as isize;
        let (def_b, def_i) = defs.get(r).unwrap();
        let def = &blocks[*def_b].instructions[*def_i];
        let r_uses = uses
            .get(r)
            .unwrap()
            .iter()
            .map(|(_, b, i)| &blocks[*b].instructions[*i])
            .collect::<Vec<_>>();

        let cost: isize = if def.is_load() && r_uses.iter().all(|i| i.is_store()) {
            -1
        } else {
            let loop_costs: usize = uses
                .get(r)
                .unwrap()
                .iter()
                .map(|(l, _, _)| 10_usize.pow(loop_map.level_of_nesting(l)))
                .sum();

            // TODO: this already is set.len() * loop_cost since we sum 10^nesting and get at least
            // 1 for each use.
            (set.len() * loop_costs) as isize
        };
        // Just remove the fact that we multiplied by out degree
        let curr = cost / degree;

        if curr < best {
            best_idx = idx;
            best = curr;
        }
    }

    graph.remove(best_idx).unwrap()
}

pub fn build_ranges(
    blocks: &[Block],
    domtree: &DominatorTree,
    exit: &OrdLabel,
    start: &OrdLabel,
    loop_map: &LoopAnalysis,
) {
    let mut phis: BTreeMap<_, BTreeSet<_>> = BTreeMap::new();
    let mut use_map: BTreeMap<_, Vec<_>> = BTreeMap::new();
    let mut def_map: BTreeMap<_, _> = BTreeMap::new();
    for (b, (label, blk)) in reverse_postorder(&domtree.cfg_succs_map, start)
        .filter_map(|label| {
            Some((label, blocks.iter().find(|b| b.label.starts_with(label.as_str()))?))
        })
        .enumerate()
    {
        for (i, inst) in blk.instructions.iter().enumerate() {
            if matches!(inst, Instruction::Skip(..)) {
                continue;
            }
            if let Instruction::Phi(reg, set, subs) = inst {
                let subs = subs.unwrap();
                let mut phi = *reg;
                phi.as_phi(subs);
                if def_map.insert(phi, (b, i)).is_some() {
                    panic!("Should not be overlaping register names {} {:?}", blk.label, inst)
                }
                let cur_phi = phis.entry(reg).or_default();
                *cur_phi = cur_phi.union(set).cloned().collect();
            } else if let Some(dst) = inst.target_reg() {
                if def_map.insert(*dst, (b, i)).is_some() {
                    panic!("Should not be overlaping register names {} {:?}", blk.label, inst)
                }
            }
            for operand in inst.operand_iter() {
                use_map.entry(operand).or_default().push((label, b, i));
            }
        }
    }

    fn build_interference(
        blocks: &[Block],
        predecessors: &HashMap<OrdLabel, BTreeSet<OrdLabel>>,
        curr: &OrdLabel,
        graph: &mut HashMap<Reg, BTreeSet<Reg>>,
        mut live_from_succ: BTreeSet<Reg>,
        seen: &mut BTreeSet<OrdLabel>,
    ) {
        println!("{}", curr.as_str());
        seen.insert(curr.clone());
        let blk_idx = blocks.iter().position(|b| b.label.starts_with(curr.as_str())).unwrap();
        for inst in blocks[blk_idx].instructions.iter().rev() {
            if matches!(inst, Instruction::Skip(..)) {
                continue;
            }

            if let Instruction::Phi(reg, set, subs) = inst {
                let subs = subs.unwrap();
                let mut phi = *reg;
                phi.as_phi(subs);
                live_from_succ.remove(&phi);

                for s in set.iter().filter(|s| **s != subs) {
                    let mut p = *reg;
                    p.as_phi(*s);
                    live_from_succ.insert(p);
                }
            } else if let Some(dst) = inst.target_reg() {
                live_from_succ.remove(dst);
            }
            for operand in inst.operand_iter() {
                live_from_succ.insert(operand);
            }
            for operand in inst.operand_iter() {
                let interfere = graph.entry(operand).or_default();
                live_from_succ.remove(&operand);
                *interfere = interfere.union(&live_from_succ).cloned().collect();
                live_from_succ.insert(operand);
            }
        }

        let empty = BTreeSet::new();
        let preds = predecessors.get(curr).unwrap_or(&empty);
        if preds.len() == 1 {}
        for pred in preds {
            if pred == curr || seen.contains(pred) {
                continue;
            }
            build_interference(blocks, predecessors, pred, graph, live_from_succ.clone(), seen);
        }
    }

    // let mut phis: BTreeMap<_, BTreeSet<Reg>> = BTreeMap::new();
    let mut interference: HashMap<_, BTreeSet<_>> = HashMap::new();
    let mut seen: BTreeSet<_> = BTreeSet::new();

    build_interference(
        blocks,
        &domtree.cfg_preds_map,
        exit,
        &mut interference,
        BTreeSet::new(),
        &mut seen,
    );

    print_maps("interference", interference.iter());
    println!();
    return;

    let mut spill: VecDeque<(_, BTreeSet<ColoredReg>)> = VecDeque::new();
    let mut graph_degree = interference.into_iter().collect::<Vec<_>>();
    graph_degree.sort_by(|a, b| a.1.len().cmp(&b.1.len()));
    let mut graph_degree: VecDeque<_> = graph_degree.into();
    while let Some((register, edges)) = graph_degree.pop_front() {
        if edges.len() < K_DEGREE {
            let reg = register;
            for (_, es) in &mut graph_degree {
                es.remove(&reg);
            }
            spill.push_front((reg, edges.into_iter().map(ColoredReg::Uncolored).collect()));
        } else {
            graph_degree.push_front((register, edges));
            let (reg, edges) =
                find_cheap_spill(&mut graph_degree, blocks, &def_map, &use_map, loop_map);
            for (_, es) in &mut graph_degree {
                es.remove(&reg);
            }
            spill.push_front((reg, edges.into_iter().map(ColoredReg::Uncolored).collect()));
        }
    }

    print_maps("spill", spill.iter().cloned());
    println!();

    let mut curr_color = WrappingInt(K_DEGREE as u8);
    // We have nodes to color or we don't and return.
    let Some((reg, node)) = spill.pop_front().map(|(reg, edges)| {
        if edges.is_empty() {
            (reg, ColorNode { color: curr_color, edges })
        } else {
            let n = ColorNode { color: curr_color, edges };
            curr_color += 1;
            (reg, n)
        }
    }) else { return; };
    let mut graph = BTreeMap::from_iter(std::iter::once((reg, node)));
    // Color the graph
    while let Some((r, edges)) = spill.pop_front() {
        if edges.is_empty() {
            graph.insert(r, ColorNode { color: curr_color, edges });
        } else {
            for e in &edges {
                let Some(es) = graph.get_mut(e.as_reg()).map(|n| &mut n.edges) else { continue; };
                es.remove(&ColoredReg::Uncolored(r));
                es.insert(ColoredReg::Colored(r, curr_color));
            }
            graph.insert(r, ColorNode { color: curr_color, edges });
            curr_color += 1;
        }
    }

    print_maps("colored", graph.iter());
    println!();
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct WrappingInt(u8);
impl AddAssign<u8> for WrappingInt {
    fn add_assign(&mut self, rhs: u8) {
        if usize::from(self.0) == K_DEGREE {
            self.0 = 0;
        } else {
            debug_assert!(usize::from(self.0) < K_DEGREE);
            self.0 += 1;
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ColoredReg {
    Uncolored(Reg),
    Colored(Reg, WrappingInt),
}
impl ColoredReg {
    pub fn as_reg(&self) -> &Reg {
        match self {
            Self::Uncolored(r) | Self::Colored(r, _) => r,
        }
    }
}
impl fmt::Debug for ColoredReg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Uncolored(r) => write!(f, "{:?}", r),
            Self::Colored(r, color) => write!(f, "({:?}, {})", r, color.0),
        }
    }
}

pub struct ColorNode {
    color: WrappingInt,
    edges: BTreeSet<ColoredReg>,
}
impl fmt::Debug for ColorNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("ColorNode").field(&self.color.0).field(&self.edges).finish()
    }
}

// PRINT HELPERS
//
// END
//
//

#[allow(unused)]
fn emit_cfg_viz(cfg: &BTreeMap<Reg, BTreeSet<Reg>>, file: &str) {
    use std::{
        collections::hash_map::DefaultHasher,
        fmt::Write,
        fs,
        hash::{Hash, Hasher},
    };

    fn str_id(s: &Reg) -> u64 {
        let mut state = DefaultHasher::default();
        s.hash(&mut state);
        state.finish()
    }

    let mut seen = HashSet::new();
    let mut buf = String::new();
    writeln!(buf, "digraph cfg {{").unwrap();
    for (n, map) in cfg {
        writeln!(buf, "{} [ label = \"Phi({})\", shape = square]", str_id(n), n).unwrap();
        seen.insert(n);
        for e in map {
            if !seen.contains(e) {
                writeln!(buf, "{} [ label = \"{}\", shape = square]", str_id(e), e).unwrap();
                seen.insert(e);
            }
            writeln!(buf, "{} -> {}", str_id(n), str_id(e)).unwrap();
        }
    }
    writeln!(buf, "}}").unwrap();
    fs::write(file, buf).unwrap();
}
