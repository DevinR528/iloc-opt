use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque},
    fmt,
    ops::{AddAssign, Range},
};

use crate::{
    iloc::{Block, Function, Instruction, Operand, Reg},
    lcm::{print_maps, LoopAnalysis},
    ralloc::K_DEGREE,
    ssa::{postorder, reverse_postorder, DominatorTree, OrdLabel},
};

const INFINITY: isize = isize::MAX;

fn all_colors() -> BTreeSet<WrappingInt> {
    (1..(K_DEGREE + 1)).into_iter().map(|i| WrappingInt::Valid(i as u8)).collect()
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum WrappingInt {
    Valid(u8),
    Invalid,
}
impl WrappingInt {
    fn int_mut(&mut self) -> &mut u8 {
        let Self::Valid(int) = self else { unreachable!("{:?}", self) };
        int
    }
    pub fn int(&self) -> &u8 {
        let Self::Valid(int) = self else { unreachable!("{:?}", self) };
        int
    }
}
impl Default for WrappingInt {
    fn default() -> Self {
        Self::Valid(1)
    }
}
impl AddAssign<u8> for WrappingInt {
    fn add_assign(&mut self, rhs: u8) {
        if usize::from(*self.int()) == K_DEGREE + 1 {
            *self.int_mut() = 1;
        } else {
            debug_assert!((usize::from(*self.int())) < K_DEGREE + 1);
            *self.int_mut() += 1;
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
    fn color(&self) -> WrappingInt {
        let Self::Colored(_, c) = self else { unreachable!("{:?}", self) };
        *c
    }

    pub(crate) fn as_color(&mut self, color: WrappingInt) {
        if let Self::Uncolored(r) = self {
            *self = Self::Colored(*r, color);
        }
    }
}
impl fmt::Debug for ColoredReg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Uncolored(r) => write!(f, "UnColored({:?})", r),
            Self::Colored(r, color) => write!(f, "Clr({:?})", color),
        }
    }
}

pub struct ColorNode {
    pub color: WrappingInt,
    edges: Vec<ColoredReg>,
}
impl fmt::Debug for ColorNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("ColorNode").field(&self.color).field(&self.edges).finish()
    }
}

pub type DefUsePair = (BTreeMap<Reg, Vec<(usize, usize)>>, BTreeMap<Reg, Vec<(usize, usize)>>);
pub fn build_use_def_map(
    domtree: &DominatorTree,
    start: &OrdLabel,
    blocks: &[Block],
) -> DefUsePair {
    let mut use_map: BTreeMap<_, Vec<_>> = BTreeMap::new();
    let mut def_map: BTreeMap<_, Vec<_>> = BTreeMap::new();
    for (b, (label, blk)) in reverse_postorder(&domtree.cfg_succs_map, start)
        .filter_map(|label| Some((label, blocks.iter().find(|b| b.label == label.as_str())?)))
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

                def_map.entry(phi).or_default().push((b, i));
            }
            if let Some(dst) = inst.target_reg() {
                def_map.entry(*dst).or_default().push((b, i));
            }
            for operand in inst.operand_iter() {
                use_map.entry(operand).or_default().push((b, i));
            }
        }
    }
    (def_map, use_map)
}

pub fn build_ranges(
    blocks: &[Block],
    domtree: &DominatorTree,
    start: &OrdLabel,
    def_map: &BTreeMap<Reg, Vec<(usize, usize)>>,
    use_map: &BTreeMap<Reg, Vec<(usize, usize)>>,
    loop_map: &LoopAnalysis,
) -> Result<(BTreeMap<Reg, ColorNode>, BTreeMap<Reg, BTreeSet<Reg>>), BTreeSet<Reg>> {
    let mut changed = true;
    let mut phi_defs: HashMap<_, HashSet<Reg>> = HashMap::new();
    let mut phi_uses: HashMap<_, HashSet<Reg>> = HashMap::new();
    let mut defs: HashMap<_, HashSet<Reg>> = HashMap::new();
    let mut uexpr: HashMap<_, HashSet<Reg>> = HashMap::new();
    while changed {
        changed = false;
        for (label, blk) in reverse_postorder(&domtree.cfg_succs_map, start)
            .filter_map(|label| Some((label, blocks.iter().find(|b| b.label == label.as_str())?)))
        {
            // TODO: this is really inefficient and ugly
            let ugh = defs.clone();

            let uloc = uexpr.entry(label.clone()).or_default();
            let def_loc = defs.entry(label.clone()).or_default();
            let phi_def_loc = phi_defs.entry(label.clone()).or_default();

            for inst in &blk.instructions {
                if matches!(inst, Instruction::Skip(..)) {
                    continue;
                }
                if let Instruction::Phi(r, set, subs) = inst {
                    let subs = subs.unwrap();
                    let mut phi = *r;
                    phi.as_phi(subs);
                    phi_def_loc.insert(phi);

                    for s in set.iter().filter(|s| **s != subs) {
                        let mut phi = *r;
                        phi.as_phi(*s);
                        // TODO: this is really inefficient and ugly
                        if let Some((l, _)) = ugh.iter().find(|(l, set)| set.contains(&phi)) {
                            phi_uses.entry(l.clone()).or_default().insert(phi);
                        }
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

    // print_maps("phi_defs", phi_defs.iter());
    // print_maps("phi_uses", phi_uses.iter());
    // print_maps("defs", defs.iter());
    // println!();

    changed = true;
    let empty = HashSet::new();
    let mut live_out: HashMap<OrdLabel, HashSet<Reg>> = HashMap::new();
    let mut live_in: HashMap<OrdLabel, HashSet<Reg>> = HashMap::new();
    while changed {
        changed = false;
        for label in postorder(&domtree.cfg_succs_map, start) {
            let empty_bset = BTreeSet::new();

            // LIVE-IN
            let phi_def = phi_defs.get(label).unwrap_or(&empty);
            let up_expr = uexpr.get(label).unwrap_or(&empty);
            let live_def_diff = live_out
                .get(label)
                .unwrap_or(&empty)
                .difference(defs.get(label).unwrap_or(&empty))
                .copied()
                .collect();

            // PhiDef(b) ∪ UpExpr(b) ∪ (LiveOut(b) - Defs(b))
            let new = phi_def
                .union(up_expr)
                .copied()
                .collect::<HashSet<_>>()
                .union(&live_def_diff)
                .copied()
                .collect();

            let old = live_in.entry(label.clone()).or_default();
            if *old != new {
                *old = new;
                changed |= true;
            }

            // live-out is
            // (∪ ∀s {s: succs b} LiveIn(s) - PhiDefs(s)) ∪ PhiUse(b)
            let mut new = domtree
                .cfg_succs_map
                .get(label) // TODO: filter exit node out
                .unwrap_or(&empty_bset)
                .iter()
                .map(|s| {
                    live_in
                        .get(s)
                        .unwrap_or(&empty)
                        .difference(phi_defs.get(s).unwrap_or(&empty))
                        .copied()
                        .collect::<HashSet<_>>()
                })
                .fold(HashSet::new(), |collect, next| collect.union(&next).copied().collect())
                .union(phi_uses.get(label).unwrap_or(&empty))
                .copied()
                .collect();

            let old = live_out.entry(label.clone()).or_default();
            if *old != new {
                *old = new;
                changed |= true;
            }
        }
    }

    // print_maps("live_in", live_in.iter());
    // print_maps("live_out", live_out.iter());
    // println!();

    let mut interference: BTreeMap<_, BTreeSet<_>> = BTreeMap::new();
    for curr in postorder(&domtree.cfg_succs_map, start) {
        let livenow = live_out.get_mut(curr).unwrap();
        let blk_idx = blocks.iter().position(|b| b.label == curr.as_str()).unwrap();
        for inst in blocks[blk_idx].instructions.iter().rev() {
            if matches!(inst, Instruction::Skip(..)) {
                continue;
            }

            if let Some(dst) = inst.target_reg() {
                for reg in &*livenow {
                    if dst == reg || matches!(dst, Reg::Phi(0, _)) || matches!(reg, Reg::Phi(0, _))
                    {
                        continue;
                    }

                    interference.entry(dst.to_register()).or_default().insert(reg.to_register());
                    interference.entry(reg.to_register()).or_default().insert(dst.to_register());
                }

                // Incase there is a register that has no overlapping live ranges
                interference.entry(dst.to_register()).or_default();
                livenow.remove(dst);
            } else if let Instruction::ImmLoad { dst, .. } = inst {
                interference.entry(dst.to_register()).or_default();
            }

            for operand in inst.operand_iter() {
                // Incase there is a register that has no overlapping live ranges
                interference.entry(operand.to_register()).or_default();
                livenow.insert(operand);
            }
        }
    }

    print_maps("interference", interference.iter().collect::<BTreeMap<_, _>>().iter());
    println!();

    let mut insert_load_store = BTreeSet::new();
    let mut color_hard_first: VecDeque<(_, Vec<ColoredReg>)> = VecDeque::new();
    let mut graph_degree = interference.clone().into_iter().collect::<Vec<_>>();
    graph_degree.sort_by(|a, b| a.1.len().cmp(&b.1.len()));
    let mut graph_degree: VecDeque<_> = graph_degree.into();
    while let Some((register, edges)) = graph_degree.pop_front() {
        if matches!(register, Reg::Phi(0, _)) {
            continue;
        }
        if edges.len() < K_DEGREE {
            let reg = register;
            for (_, es) in &mut graph_degree {
                es.remove(&reg);
            }
            color_hard_first
                .push_front((reg, edges.into_iter().map(ColoredReg::Uncolored).collect()));
        } else {
            graph_degree.push_front((register, edges));
            let (reg, edges) =
                find_cheap_spill(&mut graph_degree, blocks, def_map, use_map, loop_map);
            for (_, es) in &mut graph_degree {
                es.remove(&reg);
            }
            color_hard_first
                .push_front((reg, edges.into_iter().map(ColoredReg::Uncolored).collect()));
        }
    }

    print_maps("hard first", color_hard_first.iter().cloned());
    println!();

    let mut curr_color = WrappingInt::default();
    // We have nodes to color or we don't and return.
    let Some((reg, node)) = color_hard_first.pop_front().map(|(reg, edges)| {
            (reg, ColorNode { color: curr_color, edges })
        }) else { return Ok((BTreeMap::new(), BTreeMap::new())); };

    let mut need_to_spill = vec![];
    let mut graph = BTreeMap::from_iter(std::iter::once((reg, node)));
    // Color the graph
    while let Some((r, mut edges)) = color_hard_first.pop_front() {
        if edges.is_empty() {
            graph.insert(r, ColorNode { color: curr_color, edges });
        } else {
            // REMEMBER the mapping is
            //
            // ColorNode -> edges (Set<ColorReg>)
            let mut conflict = false;
            let mut colors = BTreeSet::new();
            for e in &mut edges {
                // Get the node that represents this register
                let Some(node) = graph.get_mut(e.as_reg()) else { continue; };
                // Color the edge the same as the node (this makes sure all edges are colored the
                // same as their node)
                e.as_color(node.color);
                // Keep track of colors we are connected to (this node can not have colors in common
                // with its edges)
                colors.insert(node.color);
            }

            if let Some(clr) = all_colors().difference(&colors).next() {
                for e in &mut edges {
                    let Some(node) = graph.get_mut(e.as_reg()) else { continue; };
                    if let Some(pos) =
                        node.edges.iter().position(|ele| *ele == ColoredReg::Uncolored(r))
                    {
                        node.edges[pos] = ColoredReg::Colored(r, *clr);
                    }
                }
                graph.insert(r, ColorNode { color: *clr, edges });
            } else {
                graph.insert(r, ColorNode { color: WrappingInt::Invalid, edges });
                need_to_spill.push(r);
            }
        }
    }

    if need_to_spill.is_empty() {
        print!("{} ", start);
        print_maps("colored", graph.iter());
        println!("{:?}", insert_load_store);
        println!();

        Ok((graph, interference))
    } else {
        print_maps("colored", graph.iter());

        for spilled in need_to_spill.drain(..) {
            insert_load_store.insert(spilled);
        }

        Err(insert_load_store)
    }
}

fn find_cheap_spill(
    graph: &mut VecDeque<(Reg, BTreeSet<Reg>)>,
    blocks: &[Block],
    defs: &BTreeMap<Reg, Vec<(usize, usize)>>,
    uses: &BTreeMap<Reg, Vec<(usize, usize)>>,
    loop_map: &LoopAnalysis,
) -> (Reg, BTreeSet<Reg>) {
    let mut best = INFINITY;
    let mut best_idx = 0;

    let empty_def = vec![];
    let empty_use = vec![];
    for (idx, (r, set)) in graph.iter().enumerate() {
        let degree = set.len() as isize;
        let defs = defs.get(r).unwrap_or(&empty_def);
        let r_defs = defs.iter().map(|(b, i)| &blocks[*b].instructions[*i]).collect::<Vec<_>>();
        let uses = uses.get(r).unwrap_or(&empty_use);
        let r_uses = uses.iter().map(|(b, i)| &blocks[*b].instructions[*i]).collect::<Vec<_>>();

        let cost: isize =
            if r_defs.iter().all(|i| i.is_load()) && r_uses.iter().all(|i| i.is_store()) {
                -1
            } else if let ([(def_block, def_inst)], [(use_block, use_inst)]) = (defs.as_slice(), uses.as_slice())
                && (def_block == use_block && *def_inst == use_inst + 1) {
                INFINITY
            } else {
                let loop_costs: usize =
                    uses.iter().map(|(b, _)| 10_usize.pow(loop_map.level_of_nesting(&OrdLabel::from_known(&blocks[*b].label)))).sum();

                // TODO: this already is set.len() * loop_cost since we sum 10^nesting and get at
                // least 1 for each use.
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
