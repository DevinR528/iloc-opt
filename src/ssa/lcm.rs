use std::{
    collections::{btree_map::Entry, BTreeMap, BTreeSet, HashMap, HashSet},
    fmt, vec,
};

use crate::{
    iloc::{Function, Instruction, Operand, Reg},
    ssa::{dfs_order, postorder, preorder, reverse_postorder, DominatorTree, OrdLabel},
};

fn print_maps<K: fmt::Debug, V: fmt::Debug>(name: &str, map: &HashMap<K, V>) {
    println!("{} {{", name);
    for (k, v) in map {
        println!("    {:?}: {:?},", k, v);
    }
    println!("}}")
}

// Critical edge - These must be split
// Critical edges are edges from a block with multiple successors to a block
// with multiple predecessors.
//
//     N
//    / \ <-- this is critical
//       \ / <-- this is another predecessor
//        C
//

pub fn lazy_code_motion(func: &mut Function, domtree: &DominatorTree, exit: &OrdLabel) {
    let start = OrdLabel::new_start(&func.label);

    let mut use_map: HashMap<_, Vec<_>> = HashMap::new();
    for (b, blk) in func.blocks.iter().enumerate() {
        for (i, inst) in blk.instructions.iter().enumerate() {
            for operand in inst.operand_iter() {
                let Some(dst) = inst.target_reg() else { continue; };
                use_map.entry(operand).or_default().push((&blk.label, *dst));
            }
        }
    }

    print_maps("uses", &use_map);

    let mut universe: HashMap<_, HashSet<Reg>> = HashMap::new();

    // This should be something like
    let mut changed = true;
    let mut dexpr: HashMap<_, HashSet<Reg>> = HashMap::new();
    let mut uexpr: HashMap<_, HashSet<Reg>> = HashMap::new();

    let mut transparent: HashMap<_, HashSet<Reg>> = HashMap::new();
    let mut kill: HashMap<OrdLabel, HashSet<Reg>> = HashMap::new();
    while changed {
        changed = false;
        for (label, blk) in reverse_postorder(&domtree.cfg_succs_map, &start).filter_map(|label| {
            #[rustfmt::skip]
            Some((
                label,
                func.blocks.iter().find(|b| b.label.starts_with(label.as_str()))?
            ))
        }) {
            let uni = universe.entry(label.clone()).or_default();

            let dloc = dexpr.entry(label.clone()).or_default();
            let uloc = uexpr.entry(label.clone()).or_default();

            let k_loc = kill.entry(label.clone()).or_default();
            for inst in &blk.instructions {
                let (a, b) = inst.operands();
                let dst = inst.target_reg();

                if let Some(t) = dst {
                    if inst.is_pre_expr() {
                        uni.insert(*t);
                        dloc.insert(*t);
                        if !k_loc.contains(t) {
                            changed |= uloc.insert(*t);
                            // `t ∉ anticipated_local` is implicit in any sets behavior
                        }
                    } else {
                        for (b, kdst) in use_map.get(t).unwrap_or(&vec![]) {
                            changed |= k_loc.insert(*kdst);
                            if b.starts_with(label.as_str()) {
                                dloc.remove(kdst);
                            }
                        }
                    }
                }
            }

            let transp = transparent.entry(label.clone()).or_default();
            let not_killed: HashSet<_> = uni.difference(k_loc).cloned().collect();
            for new in not_killed {
                changed |= transp.insert(new);
            }
        }
    }

    print_maps("universe", &universe);
    print_maps("dexpr", &dexpr);
    print_maps("uexpr", &uexpr);
    print_maps("trans", &transparent);
    print_maps("kill", &kill);
    println!();

    let empty = HashSet::new();

    // AVAILABLE
    // The expression is used in every predecessor (this is inherited so as long as it is not
    // killed it could be a non direct predecessor)
    changed = true;
    let mut avail_out: HashMap<OrdLabel, HashSet<_>> = HashMap::new();
    let mut avail_in: HashMap<OrdLabel, HashSet<_>> = HashMap::new();
    while changed {
        changed = false;
        for (label, blk) in reverse_postorder(&domtree.cfg_succs_map, &start).filter_map(|label| {
            Some((label, func.blocks.iter().find(|b| b.label.starts_with(label.as_str()))?))
        }) {
            let empty_bset = BTreeSet::new();
            // AVAILABLE-IN (only used to compute `avail_out`)
            // Empty set for anticipated-out exit block
            if label == &start {
                avail_in.insert(label.clone(), HashSet::new());
            } else {
                // Available In is all predecessors of `label`s available-out sets intersected
                // (elements common in all parents/predecessors)
                let mut sets = domtree
                    .cfg_preds_map
                    .get(label)
                    .unwrap_or(&empty_bset)
                    .iter()
                    .filter_map(|l| avail_out.get(l));

                let mut new = sets.next().cloned().unwrap_or_default();
                for rest in sets {
                    new = new.intersection(rest).cloned().collect();
                }

                let old = avail_in.entry(label.clone()).or_default();
                if *old != new {
                    *old = new;
                    changed |= true;
                }
            }

            // AVAILABLE-OUT
            // Ant_Loc(b) ∪ (Avail_In(b) ∩ !Transp(b))
            // Is equivalent to
            // Ant_Loc(b) ∪ (Avail_In(b) - Kill(b))
            let old = avail_out.entry(label.clone()).or_default();
            let new = dexpr
                .get(label)
                .unwrap_or(&empty)
                .union(
                    &avail_in
                        .get(label)
                        .unwrap_or(&empty)
                        .difference(kill.get(label).unwrap_or(&empty))
                        .cloned()
                        .collect(),
                )
                .cloned()
                .collect();
            if *old != new {
                *old = new;
                changed |= true;
            }
        }
    }

    print_maps("avail_in", &avail_in);
    print_maps("avail_out", &avail_out);
    println!();

    changed = true;
    // ANTICIPATED
    // The expression is used in all successors (this is inherited so as long as it is not
    // killed it could be a non direct successor)
    let mut anti_out: HashMap<OrdLabel, HashSet<Reg>> = HashMap::new();
    // for label in reverse_postorder(&domtree.cfg_succs_map, &start) {
    //     anti_out.insert(label.clone(), universe.get(label).cloned().unwrap_or_default());
    // }
    let mut anti_in: HashMap<OrdLabel, HashSet<Reg>> = HashMap::new();
    while changed {
        changed = false;
        for (label, blk) in
            postorder(&domtree.cfg_succs_map, &start).into_iter().filter_map(|label| {
                #[rustfmt::skip]
                Some((
                    label,
                    func.blocks.iter().find(|b| b.label.starts_with(label.as_str()))?
                ))
            })
        {
            let empty_bset = BTreeSet::new();

            // ANTICIPATED-IN
            let old = anti_in.entry(label.clone()).or_default();
            let new = uexpr
                .get(label)
                .unwrap_or(&empty)
                .union(
                    &anti_out
                        .get(label)
                        .unwrap_or(&empty)
                        .difference(kill.get(label).unwrap_or(&empty))
                        .cloned()
                        .collect(),
                )
                .cloned()
                .collect();

            if *old != new {
                *old = new;
                changed |= true;
            }

            // ANTICIPATED-OUT
            // Empty set for anticipated-out exit block
            if label == exit {
                anti_out.insert(label.clone(), HashSet::new());
            } else {
                // anticipated-out is all successors of `label`s anticipated-in sets intersected
                // (elements common in all `label`s successors siblings)
                let mut sets = domtree
                    .cfg_succs_map
                    .get(label) // TODO: filter exit node out
                    .unwrap_or(&empty_bset)
                    .iter()
                    .map(|l| anti_in.get(l).unwrap_or(&empty));

                let mut new = sets.next().cloned().unwrap_or_default();
                for rest in sets {
                    new = new.intersection(rest).cloned().collect();
                }

                let old = anti_out.entry(label.clone()).or_default();
                if *old != new {
                    *old = new;
                    changed |= true;
                }
            }
        }
    }

    print_maps("ant_in", &anti_in);
    print_maps("ant_out", &anti_out);
    println!();

    // EARLIEST
    // Based on availability (is it above me) and anticipation (is it below me) we compute the
    // furthest point this expression can be moved up to. Available is our upper limit and
    // anticipated is our lower limit so earliest gets us as close to the upper limit as we can.
    changed = true;
    let mut earliest: HashMap<(OrdLabel, OrdLabel), HashSet<Reg>> = HashMap::new();
    while changed {
        changed = false;
        for (succ, blk) in reverse_postorder(&domtree.cfg_succs_map, &start).filter_map(|label| {
            Some((label, func.blocks.iter().find(|b| b.label.starts_with(label.as_str()))?))
        }) {
            // TODO:  this maybe wrong check...
            let Some(preds) = domtree.cfg_preds_map.get(succ) else { continue; };
            for pred in preds {
                // EARLIEST
                let old = earliest.entry((pred.clone(), succ.clone())).or_default();
                if succ == &start {
                    // Ant_in(s) ∩ !Av_out(p)
                    // Is equivalent to
                    // Ant_in(s) - Av_out(p)
                    for new in anti_in
                        .get(succ)
                        .unwrap_or(&empty)
                        .difference(avail_out.get(pred).unwrap_or(&empty))
                    {
                        changed |= old.insert(*new);
                    }
                } else {
                    // Ant_in(s) ∩ !Av_out(p) ∩ (!Trans(p) ∪ !Ant_out(p))
                    // Is equivalent to
                    // Ant_in(s) - Av_out(p) ∪ (Trans(p) ∩ Ant_out(p))
                    // Ant_in(s) - Av_out(p) - (Trans(p) ∪ Ant_out(p))
                    // Or is it this one
                    //                         (Trans(p) ∩ Ant_out(p))

                    let inout: HashSet<_> = anti_in
                        .get(succ)
                        .unwrap_or(&empty)
                        .difference(avail_out.get(pred).unwrap_or(&empty))
                        .collect();
                    let transout: HashSet<_> = transparent
                        .get(pred)
                        .unwrap_or(&empty)
                        .intersection(anti_out.get(pred).unwrap_or(&empty))
                        .collect();

                    for new in inout.union(&transout) {
                        changed |= old.insert(**new);
                    }

                    let uni: HashSet<_> =
                        universe.iter().flat_map(|(_, v)| v.iter().copied()).collect();
                    let not_avout: HashSet<_> =
                        uni.difference(avail_out.get(pred).unwrap_or(&empty)).copied().collect();
                    let not_antiout: HashSet<_> =
                        uni.difference(anti_out.get(pred).unwrap_or(&empty)).copied().collect();
                    let not_transp: HashSet<_> =
                        uni.difference(transparent.get(pred).unwrap_or(&empty)).copied().collect();

                    // Ant_in(p) ∩ !Avail_out(p) ∩ (Kill(p) ∪ !Ant_out(p))
                    println!(
                        "{:?}",
                        inout.intersection(
                            &kill
                                .get(pred)
                                .unwrap_or(&empty)
                                .union(&not_antiout)
                                .collect::<HashSet<_>>()
                        )
                    );
                    println!(
                        "dragon: {:?}",
                        anti_in
                            .get(succ)
                            .unwrap_or(&empty)
                            .difference(avail_in.get(succ).unwrap_or(&empty))
                    );
                }
            }
        }
    }

    print_maps("earliest", &earliest);
    println!();

    // LATEST
    changed = true;
    let mut later: HashMap<(OrdLabel, OrdLabel), HashSet<Reg>> = HashMap::new();
    let mut later_in: HashMap<OrdLabel, HashSet<Reg>> = HashMap::new();
    while changed {
        changed = false;
        for (b_label, blk) in
            reverse_postorder(&domtree.cfg_succs_map, &start).filter_map(|label| {
                Some((label, func.blocks.iter().find(|b| b.label.starts_with(label.as_str()))?))
            })
        {
            // TODO:  this maybe wrong check...
            let Some(preds) = domtree.cfg_preds_map.get(b_label) else { continue; };
            for pred in preds {
                // LATER
                let old = later.entry((pred.clone(), b_label.clone())).or_default();
                // Ant_in(s) ∩ !Av_out(p) ∩ (!UExpr(p) ∪ !Ant_out(p))
                // Is equivalent to
                // Ant_in(s) - Av_out(p) ∪ (UExpr(p) ∩ Ant_out(p))
                let inloc: HashSet<_> = later_in
                    .get(pred)
                    .unwrap_or(&empty)
                    .difference(uexpr.get(pred).unwrap_or(&empty))
                    .copied()
                    .collect();
                let transout = earliest.get(&(pred.clone(), b_label.clone())).unwrap_or(&empty);
                for new in inloc.union(transout) {
                    changed |= old.insert(*new);
                }
            }

            // LATER-IN
            if b_label == &start {
                later_in.entry(b_label.clone()).or_default();
            } else {
                // Available In is all predecessors of `label`s available-out sets intersected
                // (elements common in all parents/predecessors)
                let mut sets =
                    preds.iter().filter_map(|l| later.get(&(l.clone(), b_label.clone())));

                let mut curr_in = sets.next().cloned().unwrap_or_default();
                for rest in sets {
                    curr_in = curr_in.intersection(rest).cloned().collect();
                }

                let old = later_in.entry(b_label.clone()).or_default();
                for new in curr_in {
                    changed |= old.insert(new);
                }
            }
        }
    }

    print_maps("later_in", &later_in);
    print_maps("later", &later);
    println!();

    // INSERT and DELETE
    changed = true;
    let mut insert: HashMap<(OrdLabel, OrdLabel), HashSet<Reg>> = HashMap::new();
    let mut delete: HashMap<OrdLabel, HashSet<Reg>> = HashMap::new();
    while changed {
        changed = false;
        for (b_label, blk) in
            reverse_postorder(&domtree.cfg_succs_map, &start).filter_map(|label| {
                Some((label, func.blocks.iter().find(|b| b.label.starts_with(label.as_str()))?))
            })
        {
            // This works as `if b_label == start { both == ∅ }`
            let Some(preds) = domtree.cfg_preds_map.get(b_label) else { continue; };

            // DELETE
            let old = delete.entry(b_label.clone()).or_default();
            let set: HashSet<_> = uexpr
                .get(b_label)
                .unwrap_or(&empty)
                .difference(later_in.get(b_label).unwrap_or(&empty))
                .collect();
            for new in set {
                changed |= old.insert(*new);
            }

            // INSERT
            for pred in preds {
                let old = insert.entry((pred.clone(), b_label.clone())).or_default();
                for new in later
                    .get(&(pred.clone(), b_label.clone()))
                    .unwrap_or(&empty)
                    .difference(later_in.get(b_label).unwrap_or(&empty))
                {
                    changed |= old.insert(*new);
                }
            }
        }
    }

    print_maps("insert", &insert);
    print_maps("delete", &delete);
    println!();
}
