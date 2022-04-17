use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    fmt, vec,
};

use crate::{
    iloc::{Block, Function, Instruction, Loc, Reg},
    lcm::find_loops,
    ssa::{postorder, rpo, DominatorTree, OrdLabel},
};

pub fn print_maps<K: fmt::Debug, V: fmt::Debug>(name: &str, map: impl Iterator<Item = (K, V)>) {
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

pub fn lazy_code_motion(func: &mut Function, domtree: &DominatorTree) {
    let start = OrdLabel::entry();
    let exit = OrdLabel::exit();

    let mut use_map: HashMap<_, Vec<_>> = HashMap::new();
    let mut dst_map: HashMap<_, _> = HashMap::new();
    for blk in &func.blocks {
        for inst in &blk.instructions {
            if let Some(dst) = inst.target_reg() {
                dst_map.insert((OrdLabel::from_known(&blk.label), *dst), inst.clone());
            }
            for operand in inst.operand_iter() {
                let Some(dst) = inst.target_reg() else { continue; };
                use_map.entry(operand).or_default().push((&blk.label, *dst));
            }
        }
    }

    // print_maps("uses", use_map.iter());

    let mut changed = true;

    // Build:
    //  - down-exposed = variables that are eval'ed in `b` and no operand is defined between the
    //    last eval and the end of the block
    //  - upward-exposed = variables that are used in `b` before any redefinition
    //  - transparent =
    let mut universe: HashMap<_, BTreeSet<Reg>> = HashMap::new();
    let mut dexpr: HashMap<_, BTreeSet<Reg>> = HashMap::new();
    let mut uexpr: HashMap<_, BTreeSet<Reg>> = HashMap::new();
    let mut transparent: HashMap<_, BTreeSet<Reg>> = HashMap::new();
    let mut kill: HashMap<OrdLabel, BTreeSet<Reg>> = HashMap::new();
    while changed {
        changed = false;
        for label in rpo(&domtree.cfg_succs_map, &start) {
            let Some(blk) = func.blocks.iter().find(|b| b.label == label.as_str()) else { continue; };

            let uni = universe.entry(label.clone()).or_default();
            let dloc = dexpr.entry(label.clone()).or_default();
            let uloc = uexpr.entry(label.clone()).or_default();
            let k_loc = kill.entry(label.clone()).or_default();

            for inst in &blk.instructions {
                if let Some(t) = inst.target_reg() {
                    uni.insert(*t);
                    dloc.insert(*t);
                    if !k_loc.contains(t) {
                        changed |= uloc.insert(*t);
                        // `t ∉ anticipated_local` is implicit in any sets behavior
                    }
                    for (b, kdst) in use_map.get(t).unwrap_or(&vec![]) {
                        changed |= k_loc.insert(*kdst);
                        if b.as_str() == label.as_str() {
                            dloc.remove(kdst);
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

    // print_maps("universe", universe.iter());
    // print_maps("dexpr", dexpr.iter());
    // print_maps("uexpr", uexpr.iter());
    // print_maps("kill", kill.iter());
    // println!();

    let empty = BTreeSet::new();

    // AVAILABLE
    // The expression is used in every predecessor (this is inherited so as long as it is
    // not killed it could be a non direct predecessor)
    changed = true;
    let mut avail_out: HashMap<OrdLabel, BTreeSet<_>> = HashMap::new();
    let mut avail_in: HashMap<OrdLabel, BTreeSet<_>> = HashMap::new();
    while changed {
        changed = false;
        for label in rpo(&domtree.cfg_succs_map, &start) {
            let empty_bset = BTreeSet::new();
            // AVAILABLE-IN (only used to compute `avail_out`)
            // Empty set for anticipated-out exit block
            if label == &start {
                avail_in.insert(label.clone(), BTreeSet::new());
            } else {
                // Available In is all predecessors of `label`s available-out sets
                // intersected (elements common in all
                // parents/predecessors)
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

    // print_maps("avail_out", avail_out.iter());
    // println!();

    changed = true;
    // ANTICIPATED
    // The expression is used in all successors (this is inherited so as long as it is not
    // killed it could be a non direct successor)
    let mut anti_out: HashMap<OrdLabel, BTreeSet<Reg>> = HashMap::new();
    let mut anti_in: HashMap<OrdLabel, BTreeSet<Reg>> = HashMap::new();
    while changed {
        changed = false;
        for label in postorder(&domtree.cfg_succs_map, &start) {
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
            if *label == exit {
                anti_out.insert(label.clone(), BTreeSet::new());
            } else {
                // anticipated-out is all successors of `label`s anticipated-in sets
                // intersected (elements common in all `label`s successors
                // siblings)
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

    // print_maps("ant_in", anti_in.iter());
    // print_maps("ant_out", anti_out.iter());
    // println!();

    // EARLIEST
    // Based on availability (is it above me) and anticipation (is it below me) we compute
    // the furthest point this expression can be moved up to. Available is our upper
    // limit and anticipated is our lower limit so earliest gets us as close to the
    // upper limit as we can.
    changed = true;
    let mut earliest: HashMap<(OrdLabel, OrdLabel), BTreeSet<Reg>> = HashMap::new();
    while changed {
        changed = false;
        for succ in rpo(&domtree.cfg_succs_map, &start) {
            // Same thing as succ != start
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
                    // Ant_in(s) - Av_out(p) - (Trans(p) ∩ Ant_out(p))
                    let inout: BTreeSet<_> = anti_in
                        .get(succ)
                        .unwrap_or(&empty)
                        .difference(avail_out.get(pred).unwrap_or(&empty))
                        .copied()
                        .collect();
                    let transout: BTreeSet<_> = transparent
                        .get(pred)
                        .unwrap_or(&empty)
                        .intersection(anti_out.get(pred).unwrap_or(&empty))
                        .copied()
                        .collect();

                    for new in inout.difference(&transout) {
                        changed |= old.insert(*new);
                    }
                }
            }
        }
    }

    // print_maps("earliest", earliest.iter());
    // println!();

    // LATEST
    changed = true;
    let mut later: HashMap<(OrdLabel, OrdLabel), BTreeSet<Reg>> = HashMap::new();
    let mut later_in: HashMap<OrdLabel, BTreeSet<Reg>> = HashMap::new();
    while changed {
        changed = false;
        for b_label in rpo(&domtree.cfg_succs_map, &start) {
            // This is the same as b_label != start
            let Some(preds) = domtree.cfg_preds_map.get(b_label) else { continue; };

            for pred in preds {
                // LATER
                let old = later.entry((pred.clone(), b_label.clone())).or_default();
                // Earliest(p, s) ∪ (LaterIn(p) ∩ !Uexpr(p))
                // Is equivalent to
                // Earliest(p, s) ∪ (LaterIn(p) - Uexpr(p))
                let inloc: BTreeSet<_> = later_in
                    .get(pred)
                    .unwrap_or(&empty)
                    .difference(uexpr.get(pred).unwrap_or(&empty))
                    .copied()
                    .collect();
                let early = earliest.get(&(pred.clone(), b_label.clone())).unwrap_or(&empty);
                for new in early.union(&inloc) {
                    changed |= old.insert(*new);
                }
            }

            // LATER-IN
            if b_label == &start {
                later_in.entry(b_label.clone()).or_default();
            } else {
                // Available In is all predecessors of `label`s available-out sets
                // intersected (elements common in all
                // parents/predecessors)
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

    // print_maps("later_in", later_in.iter());
    // print_maps("later", later.iter());
    // println!();

    // INSERT and DELETE
    changed = true;
    let mut insert: HashMap<(OrdLabel, OrdLabel), BTreeSet<Reg>> = HashMap::new();
    let mut delete: HashMap<OrdLabel, BTreeSet<Reg>> = HashMap::new();
    while changed {
        changed = false;
        for b_label in rpo(&domtree.cfg_succs_map, &start) {
            // This works as `if b_label == start { both == ∅ }`
            let Some(preds) = domtree.cfg_preds_map.get(b_label) else { continue; };

            // DELETE
            let old = delete.entry(b_label.clone()).or_default();
            let set: BTreeSet<_> = uexpr
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

    // print_maps("insert", insert.iter());
    // print_maps("delete", delete.iter());
    // println!();

    let loop_analysis = find_loops(func, domtree);

    // print_maps("loops", loop_analysis.loop_map().iter());

    let mut deleted = BTreeSet::new();
    for ((pred, succ), registers) in insert.into_iter().filter(|(_, regs)| !regs.is_empty()) {
        let mut to_move = vec![];
        for r in &registers {
            let Some(inst) = dst_map.get(&(succ.clone(), *r)) else {
                continue;
            };

            if is_invalid_move(inst) {
                // println!("[cannot move] {}", inst);
                continue;
            }

            if delete.get(&pred).map_or(false, |dset| dset.contains(r)) {
                deleted.insert((pred.clone(), *r));
                continue;
            }




            let Some(b) = func.blocks.iter().position(|b| b.label == succ.as_str()) else {
                unreachable!("{:?}", succ)
            };
            let Some(i) = func.blocks[b].instructions.iter().position(|i| i == inst) else {
                unreachable!("{:?}", (succ, &func.blocks[b]))
            };

            let can_delete = delete.get(&succ).map_or(false, |dset| dset.contains(r));
            to_move.push(if can_delete {
                deleted.insert((succ.clone(), *r));
                let inst = func.blocks[b].instructions[i].clone();
                func.blocks[b].instructions[i] =
                    Instruction::Skip(format!("[pre deleted] {}", func.blocks[b].instructions[i]));
                inst
            } else {
                func.blocks[b].instructions[i].clone()
            });
        }

        if to_move.is_empty() {
            continue;
        }

        // If pred has only one successor insert at end of pred
        // If succ has only one predecessor insert at entry to succ
        // Else edge is critical so insert block into middle of edge
        if domtree.cfg_succs_map.get(&pred).unwrap().len() == 1 {
            let Some(pred_blk) = func.blocks
                .iter_mut()
                .find(|b| b.label == pred.as_str()) else { unreachable!() };

            let end_idx =
                if pred_blk.instructions.last().map_or(false, |inst| inst.uses_label().is_some()) {
                    pred_blk.instructions.len() - 2
                } else {
                    pred_blk.instructions.len() - 1
                };

            for inst in to_move.into_iter().rev() {
                pred_blk.instructions.insert(end_idx, inst);
            }
        } else if domtree.cfg_preds_map.get(&succ).unwrap().len() == 1 {
            let Some(succ_blk) = func.blocks
                .iter_mut()
                .find(|b| b.label == succ.as_str()) else { unreachable!() };

            let start_idx = if succ_blk
                .instructions
                .last()
                .map_or(false, |inst| matches!(inst, Instruction::Frame { .. }))
            {
                2
            } else {
                1
            };

            for inst in to_move.into_iter().rev() {
                succ_blk.instructions.insert(start_idx, inst);
            }
        // This is to guard against a move of instructions from succ into pred's edge
        // actually being a move into a more nested loop
        } else {
            // println!(
            //     "p {} s {}\ns: {:#?}\np: {:#?}",
            //     pred, succ, domtree.cfg_succs_map, domtree.cfg_preds_map
            // );
            let label = format!(".pre{}{}", pred.as_str(), succ.as_str());
            let mut instructions = vec![Instruction::Label(label.clone())];
            instructions.extend(to_move);
            instructions.push(Instruction::ImmJump(Loc(succ.as_str().to_string())));
            let new_block = Block { label: label.clone(), instructions };

            let Some(pred_idx) = func.blocks
                .iter()
                .position(|b| b.label == pred.as_str()) else { unreachable!() };

            // We need to fix the label in the predecessor and add a "fallthrough" `jumpI`
            // for the case when the same edge gets more than one insertion
            if let Some(cnd_br) = func.blocks[pred_idx].instructions.last_mut() && cnd_br.uses_label() == Some(succ.as_str()) {
                *cnd_br.label_mut().unwrap() = Loc(label);
            } else {
                func.blocks[pred_idx].instructions.push(Instruction::ImmJump(Loc(label)));
            }

            let pred_idx = if pred == succ { pred_idx } else { pred_idx + 1 };
            func.blocks.insert(pred_idx, new_block);
        }
    }

    for (label, dels) in delete {
        for del in dels {
            if !deleted.contains(&(label.clone(), del)) {
                let Some(inst) = dst_map.get(&(label.clone(), del)) else {
                    unreachable!("{:?}", label)
                };

                if is_invalid_move(inst) { continue; }

                let Some(b) = func.blocks.iter().position(|b| b.label == label.as_str()) else {
                    unreachable!("{:?}", label)
                };
                let Some(i) = func.blocks[b].instructions.iter().position(|i| i == inst) else {
                    unreachable!("{:?}", (label, &func.blocks[b]))
                };
                func.blocks[b].instructions[i] =
                    Instruction::Skip(format!("[pre deleted] {}", func.blocks[b].instructions[i]));
            }
        }
    }
}

fn is_invalid_move(inst: &Instruction) -> bool {
    matches!(
        inst,
        Instruction::Call { .. }
            | Instruction::ImmCall { .. }
            | Instruction::ImmRCall { .. }
            | Instruction::Load { .. }
            // | Instruction::I2I { .. }
            | Instruction::I2F { .. }
            | Instruction::F2I { .. }
            | Instruction::F2F { .. }
        )
        || matches!(inst, Instruction::I2I { src, .. } if *src != Reg::Var(0))
}
