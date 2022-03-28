use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque},
    fmt,
    ops::{AddAssign, Range},
};

use crate::{
    iloc::{Block, Function, Instruction, Operand, Reg},
    lcm::{print_maps, LoopAnalysis},
    ssa::{reverse_postorder, DominatorTree, OrdLabel},
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
    defs: &BTreeMap<Reg, (usize, usize, usize)>,
    uses: &BTreeMap<Reg, Vec<(&OrdLabel, usize, usize, usize)>>,
    loop_map: &LoopAnalysis,
) -> (Reg, BTreeSet<Reg>) {
    let mut best = 10000000000_isize;
    let mut best_idx = 0;

    for (idx, (r, set)) in graph.iter().enumerate() {
        let degree = set.len() as isize;
        let (_, def_b, def_i) = defs.get(r).unwrap();
        let def = &blocks[*def_b].instructions[*def_i];
        let r_uses = uses
            .get(r)
            .unwrap()
            .iter()
            .map(|(_, _, b, i)| &blocks[*b].instructions[*i])
            .collect::<Vec<_>>();

        let cost: isize = if def.is_load() && r_uses.iter().all(|i| i.is_store()) {
            -1
        } else {
            let loop_costs: usize = uses
                .get(r)
                .unwrap()
                .iter()
                .map(|(l, _, _, _)| 10_usize.pow(loop_map.level_of_nesting(l)))
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
    start: &OrdLabel,
    loop_map: &LoopAnalysis,
) {
    let mut range_count = 0;
    let mut phis: BTreeMap<_, BTreeSet<_>> = BTreeMap::new();
    let mut use_map: BTreeMap<_, Vec<_>> = BTreeMap::new();
    let mut def_map: BTreeMap<_, _> = BTreeMap::new();
    for (b, (label, blk)) in reverse_postorder(&domtree.cfg_succs_map, start)
        .filter_map(|label| {
            #[rustfmt::skip]
        Some((
            label,
            blocks.iter().find(|b| b.label.starts_with(label.as_str()))?
        ))
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
                if def_map.insert(phi, (range_count, b, i)).is_some() {
                    panic!("Should not be overlaping register names {} {:?}", blk.label, inst)
                }

                let cur_phi = phis.entry(reg).or_default();
                *cur_phi = cur_phi.union(set).cloned().collect();
                // for s in set.iter().filter(|s| **s != subs) {
                //     let mut p = *reg;
                //     p.as_phi(*s);
                //     use_map.entry(p).or_default().push((label, range_count, b, i));
                // }
            } else if let Some(dst) = inst.target_reg() {
                if def_map.insert(*dst, (range_count, b, i)).is_some() {
                    panic!("Should not be overlaping register names {} {:?}", blk.label, inst)
                }
            }

            for operand in inst.operand_iter() {
                use_map.entry(operand).or_default().push((label, range_count, b, i));
            }

            range_count += 1;
        }
    }

    print_maps("use", use_map.iter());
    print_maps("def", def_map.iter());
    print_maps("phis", phis.iter());
    println!();

    let mut live_ranges: BTreeMap<_, _> = BTreeMap::new();
    for (def, (rng_start, d_b, d_i)) in &def_map {
        for (u_label, use_rng, u_b, u_i) in use_map.get(def).unwrap_or(&vec![]) {
            live_ranges
                .entry(def)
                .or_insert_with(|| RegisterRange::new(*def, *rng_start))
                .add_range(*use_rng, *u_b, *u_i);
        }
    }
    let mut sort = live_ranges.iter().collect::<Vec<_>>();
    sort.sort_by(|a, b| a.1.range.start.cmp(&b.1.range.start));

    print_maps("ranges", sort.iter().cloned());
    println!();

    let mut sorted = live_ranges.values().collect::<Vec<_>>();
    sorted.sort_by(|a, b| a.range.start.cmp(&b.range.start));

    // Build the interference graph
    let mut interference: BTreeMap<_, BTreeSet<_>> = BTreeMap::new();
    let mut intrf_counts: BTreeMap<_, usize> = BTreeMap::new();
    for (idx, reg) in sorted.iter().enumerate() {
        for (i, reg_b) in sorted.iter().enumerate() {
            // No need to interfere with ourselves
            if idx == i {
                continue;
            }

            if reg_b.range.contains(&reg.range.start)
                || reg_b.range.contains(&reg.range.end)
                // Now the other way round, since `3..6` interferes with `4..6`
                || reg.range.contains(&reg_b.range.start)
                || reg.range.contains(&reg_b.range.end)
            {
                interference.entry(reg.reg).or_default().insert(reg_b.reg);
                (*intrf_counts.entry(reg_b.reg).or_default()) += 1;
            }
        }
    }

    print_maps("counts", intrf_counts.iter());
    print_maps("interference", interference.iter());
    println!();

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
                let es = &mut graph.get_mut(e.as_reg()).unwrap().edges;
                es.remove(&ColoredReg::Uncolored(r));
                es.insert(ColoredReg::Colored(r, curr_color));
            }
            graph.insert(r, ColorNode { color: curr_color, edges });
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
            Self::Uncolored(r) => write!(f, "{}", r),
            Self::Colored(r, color) => write!(f, "({}, {})", r, color.0),
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
