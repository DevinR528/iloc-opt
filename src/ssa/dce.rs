use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};

use crate::{
    iloc::{Function, Instruction, Loc, Val},
    ssa::{ControlFlowGraph, DominatorTree},
};

impl Instruction {
    fn is_critical(&self) -> bool {
        matches!(
            self,
            Instruction::ImmRet(..)
                | Instruction::Ret
                | Instruction::IRead(..)
                | Instruction::IWrite(..)
                | Instruction::SWrite(..)
                | Instruction::FRead(..)
                | Instruction::FWrite(..)
                | Instruction::I2I { .. }
                | Instruction::I2F { .. }
                | Instruction::F2I { .. }
                | Instruction::F2F { .. }
                | Instruction::Store { .. }
                | Instruction::StoreAdd { .. }
                | Instruction::StoreAddImm { .. }
                | Instruction::Jump(..)
                | Instruction::ImmJump(..)
                | Instruction::Call { .. }
                | Instruction::ImmCall { .. }
                // | Instruction::CbrT { .. }
                // | Instruction::CbrF { .. }
                // | Instruction::CbrEQ { .. }
                // | Instruction::CbrNE { .. }
                // | Instruction::CbrGT { .. }
                // | Instruction::CbrGE { .. }
                // | Instruction::CbrLT { .. }
                // | Instruction::CbrLE { .. }
                | Instruction::ImmLoad { src: Val::Location(..), .. } // | Instruction::Load { .. }
        )
    }
}

pub fn dead_code(func: &mut Function, _cfg: &mut ControlFlowGraph, domtree: &DominatorTree) {
    // println!(
    //     "preds: {:#?}\nctrl: {:#?}\ndom front: {:#?}",
    //     domtree.dom_preds_map, domtree.ctrl_dep_map, domtree.dom_frontier_map
    // );
    let mut stack = VecDeque::new();
    let mut critical_map = HashSet::new();
    let mut def_map = HashMap::new();

    let mut copied_blocks = vec![];
    for blk in &func.blocks {
        copied_blocks.push((
            blk.label.replace(':', ""),
            blk.instructions()
                // .map(|i| i.remove_phi_reg())
                .cloned()
                .collect::<Vec<_>>(),
        ));
    }
    for (b_label, blk) in &copied_blocks {
        for inst in blk {
            if inst.is_critical() {
                println!("critical {:?}", inst);
                critical_map.insert(inst);
                stack.push_back((inst, b_label));
            }
            if let Some(reg) = inst.target_reg() {
                def_map.insert(reg, (inst, b_label));
            } else if let Instruction::ImmRet(reg) | Instruction::ImmCall { ret: reg, .. } = inst {
                def_map.insert(reg, (inst, b_label));
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
            Instruction::ImmCall { args, .. } => {
                for (inst, blk) in args.iter().filter_map(|r| def_map.get(r)) {
                    if critical_map.insert(inst) {
                        stack.push_back((inst, blk));
                    }
                }
            }
            Instruction::Call { args, .. } => {
                for (inst, blk) in args.iter().filter_map(|r| def_map.get(r)) {
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

        for blk in domtree.ctrl_dep_map.get(b_label).unwrap_or(&empty) {
            println!("{} {}", blk, b_label);
            let Some(block) = func.blocks.iter().find(|b| b.label.starts_with(blk)) else { continue; };
            let Some(last_inst) = block.instructions.iter().find(|i|
                matches!(i, Instruction::ImmJump(..) | Instruction::Jump(..)) || i.is_cnd_jump()
            ) else { continue; };

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
                    println!("rewrite branch {:#?} {:?} {}", domtree, inst, blk.label);
                    jumps.push((b, i, Instruction::ImmJump(Loc("".into()))));
                } else if !matches!(inst, Instruction::ImmJump(..)) {
                    println!("remove {:?}", inst);
                    remove.push((b, i));
                }
            }
        }
    }

    for (b, i) in remove {
        func.blocks[b].instructions[i] =
            Instruction::Skip(format!("[ssadce] {}", func.blocks[b].instructions[i]));
    }
}
