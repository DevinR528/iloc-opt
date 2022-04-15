use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque},
    fmt,
    ops::{AddAssign, Range}, process::Command,
};

use crate::{
    iloc::{Block, Function, Instruction, Operand, Reg},
    lcm::{print_maps, LoopAnalysis},
    ralloc::{emit_good_ralloc_viz, emit_ralloc_viz, K_DEGREE},
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
    fn default() -> Self { Self::Valid(1) }
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

pub type DefUsePair = (BTreeMap<Reg, BTreeSet<(usize, usize)>>, BTreeMap<Reg, BTreeSet<(usize, usize)>>);
pub fn build_use_def_map(
    domtree: &DominatorTree,
    start: &OrdLabel,
    blocks: &[Block],
) -> DefUsePair {
    let mut use_map: BTreeMap<_, BTreeSet<_>> = BTreeMap::new();
    let mut def_map: BTreeMap<_, BTreeSet<_>> = BTreeMap::new();
    for (b, blk) in blocks.iter().enumerate() {

        for (i, inst) in blk.instructions.iter().enumerate() {
            if matches!(inst, Instruction::Skip(..)) {
                continue;
            }
            match inst {
                Instruction::Phi(reg, set, subs) => {
                    let subs = subs.unwrap();
                    let mut phi = *reg;
                    phi.as_phi(subs);

                    def_map.entry(phi).or_default().insert((b, i));
                }
                Instruction::Frame { params, .. } => {
                    for p in params {
                        def_map.entry(*p).or_default().insert((b, i));
                    }
                }
                _ => (),
            }
            if let Some(dst) = inst.target_reg() {
                def_map.entry(*dst).or_default().insert((b, i));
            }
            for operand in inst.operand_iter() {
                use_map.entry(operand).or_default().insert((b, i));
            }
        }
    }
    (def_map, use_map)
}

#[derive(Debug, Default)]
pub struct ColoredGraph {
    pub graph: BTreeMap<Reg, ColorNode>,
    pub interference: BTreeMap<Reg, BTreeSet<Reg>>,
    pub defs: BTreeMap<Reg, BTreeSet<(usize, usize)>>
}

#[derive(Debug, Default)]
pub struct FailedColoring {
    pub insert_spills: BTreeSet<Reg>,
    pub uses: BTreeMap<Reg, BTreeSet<(usize, usize)>>,
    pub defs: BTreeMap<Reg, BTreeSet<(usize, usize)>>
}


/// The `Ok` variant is the successfully colored graph and the original interference graph
/// (this is debug mostly), The `Err` variant is the set of registers that failed to
/// color.
pub type InterfereResult =
    Result<ColoredGraph, FailedColoring>;
pub fn build_interference(
    blocks: &mut [Block],
    domtree: &DominatorTree,
    start: &OrdLabel,
    loop_map: &LoopAnalysis,
) -> InterfereResult {
    //
    // For a node `q` in CFG a variable `v` is live-in at `q` if there is a path, not containing the
    // definition of `v`, from `q` to a  node where v is used. IT is live-out at `q` if it is
    // live-in at some successor of `q`.
    //
    //

    let mut changed = true;

    let mut phi_defs: BTreeMap<_, BTreeSet<Reg>> = BTreeMap::new();
    let mut phi_uses: BTreeMap<_, BTreeSet<Reg>> = BTreeMap::new();
    let mut phi_map: BTreeMap<_, BTreeSet<_>> = BTreeMap::new();

    let mut defs: BTreeMap<_, BTreeSet<Reg>> = BTreeMap::new();
    let mut uexpr: BTreeMap<_, BTreeSet<Reg>> = BTreeMap::new();
    while changed {
        changed = false;
        for label in reverse_postorder(&domtree.cfg_succs_map, start) {
            let blk_idx = blocks.iter().position(|b| b.label == label.as_str()).unwrap();
            // TODO: this is really inefficient and ugly
            let ugh = defs.clone();

            let uloc = uexpr.entry(label.clone()).or_default();
            let def_loc = defs.entry(label.clone()).or_default();
            let phi_def_loc = phi_defs.entry(label.clone()).or_default();

            for inst in blocks[blk_idx].instructions.iter() {
                if matches!(inst, Instruction::Skip(..)) {
                    continue;
                }

                for op in inst.operand_iter() {
                    if matches!(op, Reg::Phi(0, _) | Reg::Var(0)) { continue; }

                    if !def_loc.contains(&op) {
                        // We found a use without a definition above it
                        changed |= uloc.insert(op);
                    }
                }
                // All "kill" is after up_exposed
                if let Some(t) = inst.target_reg() {
                    def_loc.insert(*t);
                }

                match inst {
                    Instruction::Phi(r, set, subs) => {
                        let subs = subs.unwrap();
                        let mut phi = *r;
                        phi.as_phi(subs);

                        phi_def_loc.insert(phi);

                        // Make this the new name
                        let phi_set = phi_map.entry(phi).or_default();
                        for s in set.iter().filter(|s| **s != subs) {
                            let mut phi = *r;
                            phi.as_phi(*s);

                            phi_set.insert(phi);
                            // TODO: this is really inefficient and ugly
                            if let Some((l, _)) = ugh.iter().find(|(l, set)| set.contains(&phi)) {
                                phi_uses.entry(l.clone()).or_default().insert(phi);
                            }
                        }
                        let mut move_to = BTreeMap::new();
                        for ((a, aset), (b, bset)) in phi_map.iter().zip(phi_map.iter().skip(1)) {
                            // This is checking `is_intersection` basically
                            // if there are common elements
                            if !aset.is_disjoint(bset) {
                                move_to.insert(*a, *b);
                            }
                        }
                        for (a, b) in move_to {
                            let Some(edges) = phi_map.remove(&b) else { continue; };
                            let pm = phi_map.entry(a).or_default();
                            pm.insert(b);
                            for e in edges {
                                pm.insert(e);
                            }
                        }
                    }
                    Instruction::Frame { params, .. } => {
                        for p in params {
                            def_loc.insert(*p);
                        }
                    }
                    _ => (),
                }
            }
        }
    }

    // print_maps("phi_defs", phi_defs.iter());
    // print_maps("phi_uses", phi_uses.iter());
    // print_maps("upexpo", uexpr.iter());
    // println!();

    changed = true;
    let empty = BTreeSet::new();
    let mut live_out: BTreeMap<OrdLabel, BTreeSet<Reg>> = BTreeMap::new();
    let mut live_in: BTreeMap<OrdLabel, BTreeSet<Reg>> = BTreeMap::new();
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
                .collect::<BTreeSet<_>>()
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
                        .collect::<BTreeSet<_>>()
                })
                .fold(BTreeSet::new(), |collect, next| collect.union(&next).copied().collect())
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

    print_maps("live_in", live_in.iter());
    print_maps("live_out", live_out.iter());
    println!();

    // Mapping of the `Reg::Phi` name we chose and all `Reg::Phi`s connected to it by
    // `Instruction::Phi` nodes
    let connected_phis: BTreeMap<Reg, Reg> = phi_map.iter()
        .flat_map(|(k, set)| set.iter().copied().chain(Some(*k)).map(|r| (r, *k)))
        .collect();
    let mut map = BTreeMap::new();

    let mut interference: BTreeMap<_, BTreeSet<_>> = BTreeMap::new();
    for block in postorder(&domtree.cfg_succs_map, start) {
        let livenow = live_out.get_mut(block).unwrap();
        let blk_idx = blocks.iter().position(|b| b.label == block.as_str()).unwrap();
        for inst in blocks[blk_idx].instructions.iter_mut().rev() {
            if matches!(inst, Instruction::Skip(..)) {
                continue;
            }

            if let Some(dst) = inst.target_reg() {
                let dst_new_name = if let Some(new_name) = connected_phis.get(dst) {
                    let len = map.len() + 1;
                    *map.entry(*new_name).or_insert(Reg::Var(len))
                } else {
                    let len = map.len() + 1;
                    *map.entry(*dst).or_insert(Reg::Var(len))
                };
                for reg in &*livenow {
                    if dst == reg || matches!(dst, Reg::Phi(0, _)) || matches!(reg, Reg::Phi(0, _))
                    {
                        continue;
                    }

                    let reg_new_name = if let Some(new_name) = connected_phis.get(reg) {
                        let len = map.len() + 1;
                        *map.entry(*new_name).or_insert(Reg::Var(len))
                    } else {
                        let len = map.len() + 1;
                        *map.entry(*reg).or_insert(Reg::Var(len))
                    };

                    interference.entry(dst_new_name).or_default().insert(reg_new_name);
                    interference.entry(reg_new_name).or_default().insert(dst_new_name);
                }
                // Incase there is a register that has no overlapping live ranges
                interference.entry(dst_new_name).or_default();
                livenow.remove(dst);
            }
            for operand in inst.operand_iter() {
                if matches!(operand, Reg::Phi(0, _) | Reg::Var(0)) { continue; }

                let operand_new_name = if let Some(new_name) = connected_phis.get(&operand) {
                    let len = map.len() + 1;
                    *map.entry(*new_name).or_insert(Reg::Var(len))
                } else {
                    let len = map.len() + 1;
                    *map.entry(operand).or_insert(Reg::Var(len))
                };
                // Incase there is a register that has no overlapping live ranges
                interference.entry(operand_new_name).or_default();
                livenow.insert(operand);
            }

            // Now remap the names of the register in the instructions
            for r in inst.registers_mut_iter() {
                if matches!(r, Reg::Phi(0, _) | Reg::Var(0)) {
                    *r = Reg::Var(0);
                    continue;
                }

                let reg = if let Some(new_name) = connected_phis.get(r) { *new_name } else { *r };
                *r = *map.get(&reg).unwrap_or_else(|| panic!("{:?}", r));
            }
        }
    }

    let (def_map, use_map) = build_use_def_map(domtree, start, &*blocks);

    // println!();
    // print_maps("phi_map", phi_map.iter());
    print_maps("def_map", def_map.iter());
    print_maps("use_map", use_map.iter());
    print_maps("interference", interference.iter().collect::<BTreeMap<_, _>>().iter());
    println!();

    // let mut still_good = true;
    let mut color_hard_first: VecDeque<(_, Vec<ColoredReg>)> = VecDeque::new();
    let mut graph_degree = interference.clone().into_iter().collect::<Vec<_>>();
    graph_degree.sort_by(|a, b| a.1.len().cmp(&b.1.len()));
    let mut graph_degree: VecDeque<_> = graph_degree.into();
    while let Some((register, edges)) = graph_degree.pop_front() {
        if matches!(register, Reg::Phi(0, _)) { continue; }
        // // TODO: is `still_good` how it works
        // if edges.len() < K_DEGREE && still_good {
        //     let reg = register;
        //     for (_, es) in &mut graph_degree {
        //         es.remove(&reg);
        //     }
        //     color_hard_first
        //         .push_front((reg,
        //     edges.into_iter().map(ColoredReg::Uncolored).collect()));
        // } else {
        //     still_good = false;
        graph_degree.push_front((register, edges));
        let (reg, edges) = find_cheap_spill(&mut graph_degree, blocks, &def_map, &use_map, loop_map);
        for (_, es) in &mut graph_degree {
            es.remove(&reg);
        }
        color_hard_first.push_front((reg, edges.into_iter().map(ColoredReg::Uncolored).collect()));
        // }
    }

    print_maps("hard first", color_hard_first.iter().cloned());
    println!();

    let mut curr_color = WrappingInt::default();
    // We have nodes to color or we don't and return.
    let Some((reg, node)) = color_hard_first.pop_front().map(|(reg, edges)| {
            (reg, ColorNode { color: curr_color, edges })
        }) else { return Ok(ColoredGraph::default()) };

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
                // Color the edge the same as the node (this makes sure all edges are
                // colored the same as their node)
                e.as_color(node.color);
                // Keep track of colors we are connected to (this node can not have colors
                // in common with its edges)
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

    // emit_ralloc_viz(
    //     &domtree.cfg_succs_map,
    //     start,
    //     blocks,
    //     &graph,
    //     &interference,
    //     // &def_map
    //     //     .iter()
    //     //     .map(|(k, v)| (*k, v.iter().cloned().collect()))
    //     //     .collect::<BTreeMap<_, Vec<_>>>(),
    //     "boo",
    // );
    // Command::new("dot")
    //     .args(["-Tpdf", "boo.dot", "-o", "boo.pdf"])
    //     .spawn()
    //     .expect("failed to execute process");
    // Command::new("firefox")
    //     .arg("boo.pdf")
    //     .spawn()
    //     .expect("failed to execute process");

    if need_to_spill.is_empty() {
        print!("{} ", start);
        print_maps("colored", graph.iter());
        println!();

        Ok(ColoredGraph { graph, interference, defs: def_map, })
    } else {
        print_maps("colored", graph.iter());

        let mut insert_load_store = BTreeSet::new();
        for spilled in need_to_spill.drain(..) {
            insert_load_store.insert(spilled);
        }

        Err(FailedColoring { insert_spills: insert_load_store, uses: use_map, defs: def_map })
    }
}

fn find_cheap_spill(
    graph: &mut VecDeque<(Reg, BTreeSet<Reg>)>,
    blocks: &[Block],
    defs: &BTreeMap<Reg, BTreeSet<(usize, usize)>>,
    uses: &BTreeMap<Reg, BTreeSet<(usize, usize)>>,
    loop_map: &LoopAnalysis,
) -> (Reg, BTreeSet<Reg>) {
    let mut best = INFINITY;
    let mut best_idx = 0;

    let empty = BTreeSet::new();
    for (idx, (r, set)) in graph.iter().enumerate() {
        let degree = usize::max(1, set.len()) as isize;
        let defs: Vec<_> = defs.get(r).unwrap_or(&empty).iter().collect();
        let r_defs = defs.iter().map(|(b, i)| &blocks[*b].instructions[*i]).collect::<Vec<_>>();
        let uses: Vec<_> = uses.get(r).unwrap_or(&empty).iter().collect();
        let r_uses = uses.iter().map(|(b, i)| &blocks[*b].instructions[*i]).collect::<Vec<_>>();

        let cost: isize = if (!r_defs.is_empty() && !r_uses.is_empty())
            && (r_defs.iter().all(|i| i.is_load()) && r_uses.iter().all(|i| i.is_store()))
        {
            -1
        } else {
            match (defs.as_slice(), uses.as_slice()) {
                ([(def_block, def_inst)], [(use_block, use_inst), ..])
                    if (def_block == use_block && def_inst + 1 == *use_inst) =>
                {
                    INFINITY
                }
                _ => {
                    let loop_costs: usize = uses
                        .iter()
                        .chain(defs.iter())
                        .map(|(b, _)| {
                            10_usize.pow(
                                loop_map.level_of_nesting(&OrdLabel::from_known(&blocks[*b].label)),
                            )
                        })
                        .sum();
                    (loop_costs * 3) as isize
                }
            }
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


//
//
//
//
// Standard algorithm for computing interference, which is broken for SSA numbered things

// let mut upvar: BTreeMap<_, BTreeSet<Reg>> = BTreeMap::new();
// let mut varkill: BTreeMap<_, BTreeSet<Reg>> = BTreeMap::new();
// for (label, blk) in reverse_postorder(&domtree.cfg_succs_map, start)
//     .filter_map(|label| Some((label, blocks.iter().find(|b| b.label == label.as_str())?)))
// {
//     let uvar = upvar.entry(label.clone()).or_default();
//     let kill = varkill.entry(label.clone()).or_default();
//     for inst in &blk.instructions {
//         if matches!(inst, Instruction::Skip(..)) {
//             continue;
//         }
//         match inst {
//             Instruction::Frame { params, .. } => {
//                 for p in params {
//                     // uvar.insert(*p);
//                     kill.insert(*p);
//                 }
//                 continue;
//             }
//             Instruction::Phi(r, set, subs) => {
//                 let subs = subs.unwrap();
//                 let mut phi = *r;
//                 phi.as_phi(subs);
//                 kill.insert(phi);
//             }
//             _ => (),
//         }

//         for op in inst.operand_iter() {
//             if matches!(op, Reg::Phi(0, _) | Reg::Var(0)) {
//                 continue;
//             }

//             if !kill.contains(&op) {
//                 // We found a use without a definition above it
//                 uvar.insert(op);
//             }
//         }

//         if let Some(t) = inst.target_reg() {
//             kill.insert(*t);
//         }
//     }
// }
// print_maps("up_exposed", upvar.iter());
// print_maps("var_kill", varkill.iter());
// println!();

// let empty = BTreeSet::new();
// let mut changed = true;
// let mut live_out: BTreeMap<_, BTreeSet<Reg>> = BTreeMap::new();
// while changed {
//     changed = false;
//     for label in postorder(&domtree.cfg_succs_map, start) {
//         let mut merge = BTreeSet::new();
//         for succ in domtree.cfg_succs_map.get(label).unwrap_or(&BTreeSet::new()) {
//             let live_out_diff_kill = live_out
//                 .get(succ)
//                 .unwrap_or(&empty)
//                 .difference(varkill.get(succ).unwrap_or(&empty))
//                 .copied()
//                 .collect();
//             let upvar_and_liveout =
//                 upvar.get(succ).unwrap_or(&empty).union(&live_out_diff_kill).copied().collect();

//             merge = merge.union(&upvar_and_liveout).copied().collect();
//         }

//         let curr = live_out.entry(label.clone()).or_default();
//         if merge != *curr {
//             changed = true;
//             *curr = merge;
//         }
//     }
// }

// changed = true;
// let mut interfere: BTreeMap<_, BTreeSet<Reg>> = BTreeMap::new();
// while changed {
//     changed = false;
//     for label in postorder(&domtree.cfg_succs_map, start) {
//         let blk_idx = blocks.iter().position(|b| b.label == label.as_str()).unwrap();

//         let live = live_out.entry(label.clone()).or_default();
//         for inst in blocks[blk_idx].instructions.iter().rev() {
//             if matches!(inst, Instruction::Skip(..)) {
//                 continue;
//             }

//             if let Some(dst) = inst.target_reg() {
//                 for reg in &*live {
//                     if dst == reg
//                         || matches!(dst, Reg::Phi(0, _))
//                         || matches!(reg, Reg::Phi(0, _))
//                     {
//                         continue;
//                     }
//                     changed |= interfere.entry(*reg).or_default().insert(*dst);
//                     changed |= interfere.entry(*dst).or_default().insert(*reg);
//                 }

//                 live.remove(dst);
//                 interfere.entry(*dst).or_default();
//             }

//             for op in inst.operand_iter() {
//                 if matches!(op, Reg::Phi(0, _) | Reg::Var(0)) { continue; }
//                 live.insert(op);
//             }

//             match inst {
//                 Instruction::Phi(r, set, subs) => {
//                     let subs = subs.unwrap();
//                     let mut phi = *r;
//                     phi.as_phi(subs);
//                     live.remove(&phi);
//                 }
//                 Instruction::Frame { params, .. } => {
//                     for p in params {
//                         live.remove(p);
//                     }
//                 }
//                 _ => (),
//             }
//         }
//     }
// }
