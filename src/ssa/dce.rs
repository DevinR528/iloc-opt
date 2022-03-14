use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};

use crate::{
    iloc::{Function, Instruction, Loc, Val},
    ssa::{postorder, ControlFlowGraph, DominatorTree, OrdLabel},
};

impl Instruction {
    fn is_critical(&self) -> bool {
        matches!(
            self,
            Instruction::ImmRet(..)
                | Instruction::Ret
                | Instruction::IRead(..)
                | Instruction::FRead(..)
                | Instruction::IWrite(..)
                | Instruction::SWrite(..)
                | Instruction::FWrite(..)
                | Instruction::Store { .. }
                | Instruction::StoreAdd { .. }
                | Instruction::StoreAddImm { .. }
                | Instruction::Jump(..)
                | Instruction::ImmJump(..)
                | Instruction::Call { .. }
                | Instruction::ImmCall { .. }
                | Instruction::Frame { .. }
                | Instruction::ImmLoad { src: Val::Location(..), .. }
        )
    }
}

pub fn dead_code(func: &mut Function, cfg: &mut ControlFlowGraph, domtree: &DominatorTree) {
    let mut stack = VecDeque::new();
    let mut critical_map = HashSet::new();
    let mut def_map = HashMap::new();

    let mut copied_blocks = vec![];
    for blk in &func.blocks {
        copied_blocks.push((OrdLabel::new(&blk.label), blk.instructions().collect::<Vec<_>>()));
    }
    let start_block = true;
    for (b_label, blk) in &copied_blocks {
        for &inst in blk {
            // If it's critical and we haven't seen it before
            if inst.is_critical() && critical_map.insert(inst) {
                stack.push_back((inst, b_label));
            }

            if let Some(reg) = inst.target_reg() {
                def_map.insert(*reg, (inst, b_label));
            } else {
                match inst {
                    Instruction::ImmRCall { ret: reg, .. }
                    | Instruction::ImmCall { ret: reg, .. } => {
                        def_map.insert(*reg, (inst, b_label));
                    }
                    Instruction::Frame { params: args, .. } => {
                        for reg in args {
                            def_map.insert(*reg, (inst, b_label));
                        }
                    }
                    Instruction::Phi(reg, set, Some(subs)) => {
                        let mut reg = *reg;
                        reg.as_phi(*subs);
                        def_map.insert(reg, (inst, b_label));
                    }
                    _ => {}
                }
            }
        }
    }

    let empty = BTreeSet::new();
    while let Some((inst, b_label)) = stack.pop_front() {
        let (a, b) = inst.operands();
        if let Some((a_inst, a_blk)) = a.and_then(|a| a.opt_reg()).and_then(|a| def_map.get(&a)) {
            if critical_map.insert(a_inst) {
                stack.push_back((a_inst, a_blk));
            }
        }
        if let Some((b_inst, b_blk)) = b.and_then(|b| b.opt_reg()).and_then(|b| def_map.get(&b)) {
            if critical_map.insert(b_inst) {
                stack.push_back((b_inst, b_blk));
            }
        }

        match inst {
            Instruction::Call { args, .. }
            | Instruction::ImmCall { args, .. }
            | Instruction::Frame { params: args, .. } => {
                for (inst, blk) in args.iter().filter_map(|r| def_map.get(r)) {
                    if critical_map.insert(inst) {
                        stack.push_back((inst, blk));
                    }
                }
            }
            Instruction::Phi(r, set, _) => {
                for (inst, blk) in set.iter().filter_map(|subs| {
                    let mut phi = *r;
                    phi.as_phi(*subs);
                    def_map.get(&phi)
                }) {
                    if critical_map.insert(inst) {
                        stack.push_back((inst, blk));
                    }
                }
            }
            Instruction::Store { dst, .. }
            | Instruction::StoreAddImm { dst, .. }
            | Instruction::StoreAdd { dst, .. } => {
                if let Some((inst, blk)) = def_map.get(dst) {
                    if critical_map.insert(inst) {
                        stack.push_back((inst, blk));
                    }
                }
            }
            _ => (),
        }

        // Control dependence
        // Which blocks does `b_label` control the execution of (where does this block
        // jump/branch/fall-through to)
        for blk in domtree.post_dom_frontier.get(b_label).unwrap_or(&empty) {
            // println!("dtree: {} = {:?} from: {}", blk.as_str(), last_inst, b_label.as_str());

            let Some(block) = func.blocks.iter()
                .find(|b| {
                    b.label.starts_with(blk.as_str())
                }) else {
                    println!("oh shit {}", blk.as_str());
                    continue;
                };

            // TODO: A fall through would be important also...
            let Some(last_inst) = block.instructions.iter()
                .find(|i|
                    i.is_cnd_jump() || matches!(i, Instruction::ImmJump(..))
                ) else {
                    println!("{} {:?}",blk.as_str(), block.instructions().last());
                    continue;
                };

            if critical_map.insert(last_inst) {
                stack.push_back((last_inst, blk));
            }
        }
    }

    let mut jumps = vec![];
    let mut remove = vec![];
    for (b, blk) in func.blocks.iter().enumerate() {
        for (i, inst) in
            blk.instructions.iter().enumerate().filter(|(_, i)| !matches!(i, Instruction::Skip(..)))
        {
            if !critical_map.contains(&inst) {
                if inst.is_cnd_jump() {
                    // post dominance
                    // Which blocks will for sure run next (so we can jump to it)
                    if let Some(label) = domtree
                        .post_dom_tree
                        .get(blk.label.replace(':', "").as_str())
                        .and_then(|set| if set.len() == 1 { set.iter().next() } else { None })
                    {
                        println!(
                            "rewrite branch {} jumpI -> {:?} {:#?} {:#?}",
                            inst, label, domtree.post_dom_tree, domtree.post_dom_frontier
                        );

                        jumps.push((b, i, Instruction::ImmJump(Loc(label.to_string()))));
                    }
                } else if !matches!(inst, Instruction::ImmJump(..) | Instruction::Label(..)) {
                    println!("remove {:?}", inst);
                    remove.push((b, i));
                }
            }
        }
    }

    // println!(
    //     "post_dom: {:#?}\npost_dom_front: {:#?}\n{:#?}",
    //     domtree.post_dom, domtree.post_dom_frontier, domtree.dom_frontier_map
    // );

    for (b, i) in remove {
        func.blocks[b].instructions[i] =
            Instruction::Skip(format!("[ssadce] {}", func.blocks[b].instructions[i]));
    }
    for (b, i, inst) in jumps {
        func.blocks[b].instructions[i] = inst;
    }

    cleanup(func, cfg, domtree)
}

fn cleanup(func: &mut Function, cfg: &mut ControlFlowGraph, domtree: &DominatorTree) {
    let mut cfg_map = domtree.cfg_preds_map.clone();
    let mut to_jump = vec![];
    let mut stupid_dumb_while_changed = true;
    while stupid_dumb_while_changed {
        stupid_dumb_while_changed = false;
        for blk in postorder(&cfg_map, cfg.end.as_ref().unwrap()) {
            let Some((idx, block)) = func.blocks.iter()
                .enumerate()
                .find(|(_, b)| b.label.starts_with(blk.as_str()))
                .map(|(i, b)| (i, b.clone()))
             else {
                unreachable!("unknown block {}", blk.as_str())
            };
            let fall_through = func.blocks.get(idx + 1).map(|b| b.label.to_string());
            let fall_through = fall_through.as_deref();

            let cond_branch = block.ends_with_cond_branch();
            if let Some(loc) = cond_branch {
                if Some(loc) == fall_through {
                    println!("immJump {loc} == {:?}", fall_through);

                    stupid_dumb_while_changed = true;
                    to_jump.push((idx, Instruction::ImmJump(Loc(loc.to_string()))));
                }
            }
            if let Some(loc) = block
                .ends_with_jump()
                .or_else(|| cond_branch.is_none().then(|| fall_through).flatten())
            {
                let Some(jump_to) = func.blocks.iter().find(|b| b.label.starts_with(loc)).cloned() else {
                    unreachable!("unknown block");
                };

                if block.instructions.iter().all(|i| matches!(i, Instruction::Skip(..))) {
                    stupid_dumb_while_changed = true;
                    println!("transfer {blk} to {loc}");
                    replace_transfer(func, blk.as_str(), loc, idx);
                }
                if domtree.cfg_preds_map.get(loc).map_or(false, |set| set.len() == 1) {
                    stupid_dumb_while_changed = true;
                    panic!("combine {blk} to {loc}");
                }
                if jump_to.instructions.iter().all(|i| matches!(i, Instruction::Skip(..))) {
                    stupid_dumb_while_changed = true;
                    panic!("overwrite {blk} to {loc}");
                }
            }
        }
        for (idx, inst) in to_jump.drain(0..) {
            if let Some(cbr) = func.blocks[idx].instructions.last_mut() {
                *cbr = inst;
            }
        }

        if stupid_dumb_while_changed {
            cfg_map = build_cfg(func);
        }
    }
}

pub fn build_cfg(func: &Function) -> HashMap<OrdLabel, BTreeSet<OrdLabel>> {
    let mut cfg: HashMap<_, BTreeSet<_>> = HashMap::default();
    'block: for (idx, block) in func.blocks.iter().enumerate() {
        let b_label = block.label.replace(':', "");
        // TODO: only iter the branch instructions with labels
        for inst in &block.instructions {
            // TODO: can we make note of this for optimization...(if there are trailing
            // unreachable instructions)
            if inst.is_return() {
                continue 'block;
            }

            if let Some(label) = inst.uses_label() {
                cfg.entry(OrdLabel::from_known(&b_label))
                    .or_default()
                    .insert(OrdLabel::from_known(label));
                // Skip the implicit branch to the block below the current one
                // since we found an unconditional jump.
                if inst.unconditional_jmp() {
                    continue 'block;
                }
            }
        }

        if let Some(next) = func.blocks.get(idx + 1) {
            let next_label = next.label.replace(':', "");
            cfg.entry(OrdLabel::from_known(&b_label))
                .or_default()
                .insert(OrdLabel::from_known(&next_label));
        }
    }
    cfg
}

fn replace_transfer(func: &mut Function, to: &str, with: &str, idx: usize) {
    for blk in &mut func.blocks {
        if let Some(inst) = blk.instructions.last_mut() {
            if let Some(label) = inst.label_mut() {
                if label.as_str() == to {
                    label.0 = with.to_string();
                }
            }
        }
    }
    if func.blocks[idx].label.starts_with(to) {
        func.blocks.remove(idx);
    }
}
