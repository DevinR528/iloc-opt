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

    let mut changed = true;

    let mut phi_defs: HashMap<_, HashSet<Reg>> = HashMap::new();
    let mut phi_uses: HashMap<_, HashSet<Reg>> = HashMap::new();

    let mut defs: HashMap<_, HashSet<Reg>> = HashMap::new();

    let mut uexpr: HashMap<_, HashSet<Reg>> = HashMap::new();
    while changed {
        changed = false;
        for (label, blk) in reverse_postorder(&domtree.cfg_succs_map, start).filter_map(|label| {
            Some((label, blocks.iter().find(|b| b.label.starts_with(label.as_str()))?))
        }) {
            let uloc = uexpr.entry(label.clone()).or_default();

            let def_loc = defs.entry(label.clone()).or_default();

            let phi_def_loc = phi_defs.entry(label.clone()).or_default();
            let phi_use_loc = phi_uses.entry(label.clone()).or_default();

            for inst in &blk.instructions {
                if let Instruction::Phi(r, set, subs) = inst {
                    let subs = subs.unwrap();
                    let mut phi = *r;
                    phi.as_phi(subs);
                    phi_def_loc.insert(phi);

                    for s in set.iter().filter(|s| **s != subs) {
                        let mut phi = *r;
                        phi.as_phi(*s);
                        phi_use_loc.insert(phi);
                    }
                }

                if let Some(t) = inst.target_reg() {
                    def_loc.insert(*t);
                }
                for op in inst.operand_iter() {
                    if !def_loc.contains(&op) {
                        changed |= uloc.insert(op);
                    }
                }
            }
        }
    }

    print_maps("uexpr", uexpr.iter());
    println!();

    changed = true;
    let empty = HashSet::new();
    let mut live_out: HashMap<OrdLabel, HashSet<Reg>> = HashMap::new();
    let mut live_in: HashMap<OrdLabel, HashSet<Reg>> = HashMap::new();
    while changed {
        changed = false;
        for label in postorder(&domtree.cfg_succs_map, start) {
            let empty_bset = BTreeSet::new();

            // LIVE-IN
            // PhiDef(b) ∪ UpExpr(b) ∪ (LiveOut(b) - Defs(b))
            let old = live_in.entry(label.clone()).or_default();
            let new = phi_defs
                .get(label)
                .unwrap_or(&empty)
                .union(
                    &uexpr
                        .get(label)
                        .unwrap_or(&empty)
                        .union(
                            &live_out
                                .get(label)
                                .unwrap_or(&empty)
                                .difference(defs.get(label).unwrap_or(&empty))
                                .cloned()
                                .collect(),
                        )
                        .cloned()
                        .collect(),
                )
                .cloned()
                .collect();

            if *old != new {
                *old = new;
                changed |= true;
            }

            // LIVE-OUT
            // Empty set for live-out exit block
            if label == exit {
                live_out.insert(label.clone(), HashSet::new());
            } else {
                // live-out is
                // (∪ ∀s {s: succs b} LiveIn(s) - PhiDefs(s)) ∪ PhiUse(b)
                let mut new = domtree
                    .cfg_succs_map
                    .get(label) // TODO: filter exit node out
                    .unwrap_or(&empty_bset)
                    .iter()
                    .map(|l| {
                        live_in
                            .get(l)
                            .unwrap_or(&empty)
                            .difference(phi_defs.get(l).unwrap_or(&empty))
                            .cloned()
                            .collect::<HashSet<_>>()
                    })
                    .fold(HashSet::new(), |collect, next| collect.union(&next).cloned().collect())
                    .union(phi_uses.get(label).unwrap_or(&empty))
                    .cloned()
                    .collect();

                let old = live_out.entry(label.clone()).or_default();
                if *old != new {
                    *old = new;
                    changed |= true;
                }
            }
        }
    }

    print_maps("live_in", live_in.iter());
    print_maps("live_out", live_out.iter());
    println!();

    // let mut phis: BTreeMap<_, BTreeSet<Reg>> = BTreeMap::new();
    let mut interference: HashMap<_, BTreeSet<_>> = HashMap::new();
    for curr in postorder(&domtree.cfg_succs_map, start) {
        println!("{}", curr.as_str());
        let livenow = live_out.get_mut(curr).unwrap();
        let blk_idx = blocks.iter().position(|b| b.label.starts_with(curr.as_str())).unwrap();
        for inst in blocks[blk_idx].instructions.iter().rev() {
            if matches!(inst, Instruction::Skip(..)) {
                continue;
            }

            if let Some(dst) = inst.target_reg() {
                for reg in &*livenow {
                    interference.entry(*dst).or_default().insert(*reg);
                    interference.entry(*reg).or_default().insert(*dst);
                }
                livenow.remove(dst);
            }
            for operand in inst.operand_iter() {
                livenow.insert(operand);
            }
        }
    }

    print_maps("interference", interference.iter().collect::<BTreeMap<_, _>>().iter());
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

    let mut curr_color = WrappingInt::default();
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
impl Default for WrappingInt {
    fn default() -> Self {
        Self(K_DEGREE as u8)
    }
}
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
