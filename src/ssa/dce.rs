use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};

use crate::{
    iloc::{Function, Instruction, Val},
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
                // | Instruction::I2I { .. }
                // | Instruction::I2F { .. }
                // | Instruction::F2I { .. }
                // | Instruction::F2F { .. }
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

    fn remove_phi_reg(&self) -> Self {
        match self {
            Instruction::Add { src_a, src_b, dst } => Instruction::Add {
                src_a: src_a.as_register(),
                src_b: src_b.as_register(),
                dst: dst.as_register(),
            },
            Instruction::Sub { src_a, src_b, dst } => Instruction::Sub {
                src_a: src_a.as_register(),
                src_b: src_b.as_register(),
                dst: dst.as_register(),
            },
            Instruction::Mult { src_a, src_b, dst } => Instruction::Mult {
                src_a: src_a.as_register(),
                src_b: src_b.as_register(),
                dst: dst.as_register(),
            },
            Instruction::LShift { src_a, src_b, dst } => Instruction::LShift {
                src_a: src_a.as_register(),
                src_b: src_b.as_register(),
                dst: dst.as_register(),
            },
            Instruction::RShift { src_a, src_b, dst } => Instruction::RShift {
                src_a: src_a.as_register(),
                src_b: src_b.as_register(),
                dst: dst.as_register(),
            },
            Instruction::Mod { src_a, src_b, dst } => Instruction::Mod {
                src_a: src_a.as_register(),
                src_b: src_b.as_register(),
                dst: dst.as_register(),
            },
            Instruction::Or { src_a, src_b, dst } => Instruction::Or {
                src_a: src_a.as_register(),
                src_b: src_b.as_register(),
                dst: dst.as_register(),
            },
            Instruction::And { src_a, src_b, dst } => Instruction::And {
                src_a: src_a.as_register(),
                src_b: src_b.as_register(),
                dst: dst.as_register(),
            },
            Instruction::Not { src, dst } => Instruction::Not {
                src: src.as_register(),
                dst: dst.as_register(),
            },
            Instruction::ImmAdd { src, konst, dst } => Instruction::ImmAdd {
                src: src.as_register(),
                konst: konst.clone(),
                dst: dst.as_register(),
            },
            Instruction::ImmSub { src, konst, dst } => Instruction::ImmSub {
                src: src.as_register(),
                konst: konst.clone(),
                dst: dst.as_register(),
            },
            Instruction::ImmMult { src, konst, dst } => Instruction::ImmMult {
                src: src.as_register(),
                konst: konst.clone(),
                dst: dst.as_register(),
            },
            Instruction::ImmRShift { src, konst, dst } => Instruction::ImmRShift {
                src: src.as_register(),
                konst: konst.clone(),
                dst: dst.as_register(),
            },
            Instruction::ImmLShift { src, konst, dst } => Instruction::ImmLShift {
                src: src.as_register(),
                konst: konst.clone(),
                dst: dst.as_register(),
            },
            Instruction::FAdd { src_a, src_b, dst } => Instruction::FAdd {
                src_a: src_a.as_register(),
                src_b: src_b.as_register(),
                dst: dst.as_register(),
            },
            Instruction::FSub { src_a, src_b, dst } => Instruction::FSub {
                src_a: src_a.as_register(),
                src_b: src_b.as_register(),
                dst: dst.as_register(),
            },
            Instruction::FMult { src_a, src_b, dst } => Instruction::FMult {
                src_a: src_a.as_register(),
                src_b: src_b.as_register(),
                dst: dst.as_register(),
            },
            Instruction::FDiv { src_a, src_b, dst } => Instruction::FDiv {
                src_a: src_a.as_register(),
                src_b: src_b.as_register(),
                dst: dst.as_register(),
            },
            Instruction::FComp { src_a, src_b, dst } => Instruction::FComp {
                src_a: src_a.as_register(),
                src_b: src_b.as_register(),
                dst: dst.as_register(),
            },
            Instruction::F2I { src, dst } => Instruction::F2I {
                src: src.as_register(),
                dst: dst.as_register(),
            },
            Instruction::ImmLoad { src, dst } => {
                Self::ImmLoad { src: src.clone(), dst: dst.as_register() }
            }
            Instruction::Load { src, dst } => {
                Self::Load { src: src.as_register(), dst: dst.as_register() }
            }
            Instruction::LoadAdd { src, add, dst } => Self::LoadAdd {
                src: src.as_register(),
                add: add.as_register(),
                dst: dst.as_register(),
            },
            Instruction::LoadAddImm { src, add, dst } => Self::LoadAddImm {
                src: src.as_register(),
                add: add.clone(),
                dst: dst.as_register(),
            },
            Instruction::FLoad { src, dst } => {
                Self::FLoad { src: src.as_register(), dst: dst.as_register() }
            }
            Instruction::FLoadAddImm { src,add, dst } => {
                Self::FLoadAddImm { src: src.as_register(),add: add.clone(), dst: dst.as_register() }
            }
            Instruction::Store { src, dst } => {
                Self::Store { src: src.as_register(), dst: dst.as_register() }
            }
            Instruction::StoreAdd { src, add, dst } => Self::StoreAdd {
                src: src.as_register(),
                add: add.as_register(),
                dst: dst.as_register(),
            },
            Instruction::StoreAddImm { src, add, dst } => Self::StoreAddImm {
                src: src.as_register(),
                add: add.clone(),
                dst: dst.as_register(),
            },
            Instruction::ImmRet(reg) => Instruction::ImmRet(reg.as_register()),
            Instruction::IRead(reg) => Instruction::ImmRet(reg.as_register()),
            Instruction::IWrite(reg) => Instruction::IWrite(reg.as_register()),
            Instruction::SWrite(reg) => Instruction::SWrite(reg.as_register()),
            Instruction::FRead(reg) => Instruction::FRead(reg.as_register()),
            Instruction::FWrite(reg) => Instruction::FWrite(reg.as_register()),
            Instruction::I2I { src, dst } => {
                Instruction::I2I { src: src.as_register(), dst: dst.as_register() }
            }
            Instruction::I2F { src, dst } => {
                Instruction::I2F { src: src.as_register(), dst: dst.as_register() }
            }
            Instruction::F2F { src, dst } => {
                Instruction::F2F { src: src.as_register(), dst: dst.as_register() }
            }
            Instruction::CbrT { cond, loc } => {
                Instruction::CbrT { cond: cond.as_register(), loc: loc.clone() }
            }
            Instruction::CbrF { cond, loc } => {
                Instruction::CbrF { cond: cond.as_register(), loc: loc.clone() }
            }
            Instruction::CbrEQ { a, b, loc } => {
                Instruction::CbrEQ { a: a.as_register(), b: b.as_register(), loc: loc.clone() }
            }
            Instruction::CbrNE { a, b, loc } => {
                Instruction::CbrNE { a: a.as_register(), b: b.as_register(), loc: loc.clone() }
            }
            Instruction::CbrGT { a, b, loc } => {
                Instruction::CbrGT { a: a.as_register(), b: b.as_register(), loc: loc.clone() }
            }
            Instruction::CbrGE { a, b, loc } => {
                Instruction::CbrGE { a: a.as_register(), b: b.as_register(), loc: loc.clone() }
            }
            Instruction::CbrLT { a, b, loc } => {
                Instruction::CbrLT { a: a.as_register(), b: b.as_register(), loc: loc.clone() }
            }
            Instruction::CbrLE { a, b, loc } => {
                Instruction::CbrLE { a: a.as_register(), b: b.as_register(), loc: loc.clone() }
            }
            Instruction::TestEQ { test, dst } => Instruction::TestEQ {
                test: test.as_register(),
                dst: dst.as_register(),
            },
            Instruction::TestNE { test, dst } => Instruction::TestNE {
                test: test.as_register(),
                dst: dst.as_register(),
            },
            Instruction::TestLT { test, dst } => Instruction::TestLT {
                test: test.as_register(),
                dst: dst.as_register(),
            },
            Instruction::TestLE { test, dst } => Instruction::TestLE {
                test: test.as_register(),
                dst: dst.as_register(),
            },
            Instruction::TestGT { test, dst } => Instruction::TestGT {
                test: test.as_register(),
                dst: dst.as_register(),
            },
            Instruction::TestGE { test, dst } => Instruction::TestGE {
                test: test.as_register(),
                dst: dst.as_register(),
            },
            Instruction::CmpEQ { a, b, dst } => Instruction::CmpEQ {
                a: a.as_register(),
                b: b.as_register(),
                dst: dst.as_register(),
            },
            Instruction::CmpNE { a, b, dst } => Instruction::CmpNE {
                a: a.as_register(),
                b: b.as_register(),
                dst: dst.as_register(),
            },
            Instruction::CmpLT { a, b, dst } => Instruction::CmpLT {
                a: a.as_register(),
                b: b.as_register(),
                dst: dst.as_register(),
            },
            Instruction::CmpLE { a, b, dst } => Instruction::CmpLE {
                a: a.as_register(),
                b: b.as_register(),
                dst: dst.as_register(),
            },
            Instruction::CmpGT { a, b, dst } => Instruction::CmpGT {
                a: a.as_register(),
                b: b.as_register(),
                dst: dst.as_register(),
            },
            Instruction::CmpGE { a, b, dst } => Instruction::CmpGE {
                a: a.as_register(),
                b: b.as_register(),
                dst: dst.as_register(),
            },
            Instruction::Comp { a, b, dst } => {
                Instruction::Comp { a: a.as_register(), b: b.as_register(), dst: dst.as_register() }
            }
            Instruction::Ret => Instruction::Ret,
            Instruction::Jump(reg) => Instruction::Jump(reg.as_register()),
            Instruction::ImmJump(reg) => Instruction::ImmJump(reg.clone()),
            Instruction::Call { name, args } => Instruction::Call {
                name: name.clone(),
                args: args.iter().map(|r| r.as_register()).collect(),
            },
            Instruction::ImmCall { name, args, ret } => Instruction::ImmCall {
                name: name.clone(),
                args: args.iter().map(|r| r.as_register()).collect(),
                ret: ret.as_register(),
            },
            _ => unreachable!(
                "Instruction::remove_phi_reg should never be called for a non critical instruction {:?}", self
            ),
        }
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
        copied_blocks
            .push((&blk.label, blk.instructions().map(|i| i.remove_phi_reg()).collect::<Vec<_>>()));
    }
    for (b_label, blk) in &copied_blocks {
        for inst in blk {
            if inst.is_critical() {
                println!("critical {:?}", inst);
                // let inst = inst.remove_phi_reg();
                critical_map.insert(inst);
                stack.push_back((inst, *b_label));
            }
            if let Some(reg) = inst.target_reg() {
                def_map.insert(reg.as_register(), (inst, *b_label));
            } else if let Instruction::ImmRet(reg) | Instruction::ImmCall { ret: reg, .. } = inst {
                def_map.insert(reg.as_register(), (inst, *b_label));
            }
        }
    }

    let empty = BTreeSet::new();
    while let Some((inst, b_label)) = stack.pop_front() {
        let (a, b) = inst.operands();
        if let Some((a_inst, a_blk)) = a.and_then(|a| a.opt_reg()).and_then(|a| def_map.get(&a)) {
            if !critical_map.contains(a_inst) {
                critical_map.insert(a_inst);
                stack.push_back((a_inst, a_blk));
            }
        }
        if let Some((b_inst, b_blk)) = b.and_then(|b| b.opt_reg()).and_then(|b| def_map.get(&b)) {
            if !critical_map.contains(b_inst) {
                critical_map.insert(b_inst);
                stack.push_back((b_inst, b_blk));
            }
        }

        match inst {
            Instruction::ImmCall { args, .. } => {
                for (inst, blk) in args.iter().filter_map(|r| def_map.get(r)) {
                    critical_map.insert(inst);
                    stack.push_back((inst, blk));
                }
            }
            Instruction::Call { args, .. } => {
                for (inst, blk) in args.iter().filter_map(|r| def_map.get(r)) {
                    critical_map.insert(inst);
                    stack.push_back((inst, blk));
                }
            }
            Instruction::Store { dst, .. }
            | Instruction::StoreAddImm { dst, .. }
            | Instruction::StoreAdd { dst, .. } => {
                if let Some((inst, blk)) = def_map.get(dst) {
                    critical_map.insert(inst);
                    stack.push_back((inst, blk));
                }
            }
            _ => (),
        }

        for blk in domtree.ctrl_dep_map.get(b_label).unwrap_or(&empty) {
            let Some(block) = func.blocks.iter().find(|b| b.label.starts_with(blk)) else { continue; };
            let Some(last_inst) = block.instructions.last() else { continue; };

            if !critical_map.contains(last_inst) {
                critical_map.insert(last_inst);
                stack.push_back((last_inst, blk));
            }
        }
    }

    let mut remove = vec![];
    for (b, blk) in func.blocks.iter().enumerate() {
        for (i, inst) in blk
            .instructions
            .iter()
            .enumerate()
            .filter(|(_, i)| !matches!(i, Instruction::Skip(..)))
            // TODO: this is a total waste just to keep indexes in line...
            .map(|(i, inst)| (i, inst.remove_phi_reg()))
        {
            if !critical_map.contains(&inst) {
                if inst.is_cnd_jump() {
                    println!("rewrite branch {:?}", inst);
                }

                if !matches!(inst, Instruction::ImmJump(..)) {
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
