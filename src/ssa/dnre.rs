use std::{
    collections::{BTreeSet, HashMap, VecDeque},
    ops::Range,
};

use crate::{
    iloc::{Block, Instruction, Operand, Reg},
    ssa::DominatorTree,
};

#[derive(Clone, Debug)]
pub struct RenameMeta {
    counter: usize,
    stack: VecDeque<usize>,
}
impl Default for RenameMeta {
    fn default() -> Self {
        Self { counter: 0, stack: VecDeque::from([0]) }
    }
}

fn new_name(reg: &Reg, dst: &mut Option<usize>, meta: &mut HashMap<Operand, RenameMeta>) {
    let m = meta.get_mut(&Operand::Register(*reg)).unwrap();
    m.counter += 1;
    let i = m.counter;

    m.stack.push_back(i);
    *dst = Some(i);
}
fn rewrite_name(reg: &mut Reg, meta: &RenameMeta) {
    // `unwrap_or_default` is ok here since we want a zero if the stack
    // is empty
    let phi_id = meta.stack.back().copied().unwrap();
    reg.as_phi(phi_id);
}
fn phi_range(insts: &[Instruction]) -> Range<usize> {
    0..insts.iter().take_while(|i| i.is_phi()).count()
}

pub type ScopedExprTree = VecDeque<HashMap<(Operand, Option<Operand>, String), Reg>>;

pub fn dom_val_num(
    blks: &mut [Block],
    blk_idx: usize,
    meta: &mut HashMap<Operand, RenameMeta>,
    dtree: &DominatorTree,
    expr_tree: &mut ScopedExprTree,
) {
    let ssa = unsafe { crate::SSA };
    let rng = phi_range(&blks[blk_idx].instructions);
    // The phi instructions must be filled in before their expressions are saved
    for phi in &mut blks[blk_idx].instructions[rng.clone()] {
        if let Instruction::Phi(r, _, dst) = phi {
            new_name(r, dst, meta);
        }
    }

    expr_tree.push_back(HashMap::new());

    // Remove redundant/meaningless phi instructions
    for phi in &mut blks[blk_idx].instructions[rng.clone()] {
        if let Instruction::Phi(r, set, dst) = phi {
            let phi_reg = Reg::Phi(r.as_usize(), dst.unwrap());
            let expr = (Operand::Register(phi_reg), None, "phi".to_string());
            if expr_tree.iter().find_map(|map| map.get(&expr)).is_some() {
                *phi = Instruction::Skip(format!("[redundant phi] {}", phi));
            } else {
                expr_tree.back_mut().unwrap().insert(expr, phi_reg);
                if set.len() == 1 {
                    *phi = Instruction::Skip(format!("[meaningless phi] {}", phi));
                }
            }
        } else {
            unreachable!("must be φ(x, y)")
        }
    }

    for op in &mut blks[blk_idx].instructions[rng.end..] {
        let (mut a, mut b) = op.operands_mut();
        if let Some((a, meta)) = a.as_mut().map(|reg| {
            let cpy = **reg;
            (reg, meta.entry(Operand::Register(cpy)).or_default())
        }) {
            rewrite_name(a, meta);
        }
        if let Some((b, meta)) = b.as_mut().map(|reg| {
            let cpy = **reg;
            (reg, meta.entry(Operand::Register(cpy)).or_default())
        }) {
            rewrite_name(b, meta);
        }

        // Rename registers that don't fit neatly into th operands category
        match op {
            Instruction::Call { args, .. } => {
                for arg in args {
                    let m = meta.entry(Operand::Register(*arg)).or_default();
                    rewrite_name(arg, m);
                }
            }
            Instruction::ImmCall { args, ret, .. } | Instruction::ImmRCall { args, ret, .. } => {
                for arg in args.iter_mut().chain(Some(ret)) {
                    let m = meta.entry(Operand::Register(*arg)).or_default();
                    rewrite_name(arg, m);
                }
            }
            Instruction::Store { dst, .. }
            | Instruction::StoreAdd { dst, .. }
            | Instruction::StoreAddImm { dst, .. } => {
                let m = meta.entry(Operand::Register(*dst)).or_default();
                rewrite_name(dst, m);
            }
            _ => {}
        }

        // This needs to run before we bail out for calls/stores, stuff like that...
        if let Some(dst) = op.target_reg_mut() {
            let m = meta.entry(Operand::Register(*dst)).or_default();
            // This is `new_name` minus the set addition
            m.counter += 1;
            let i = m.counter;

            m.stack.push_back(i);
            dst.as_phi(i);
        }

        if let (Some(a), b) = op.operands() {
            let expr = (a.clone(), b.clone(), op.inst_name().to_string());
            // TODO: if expr can be simplified to expr' then replace assign with `x <- expr'`

            if let Some(prev_reg) = expr_tree.iter().find_map(|map| map.get(&expr)) {
                if !op.is_tmp_expr() || op.is_call_instruction() || ssa {
                    continue;
                }

                if let Some(dst) = op.target_reg() {
                    // if dst == prev_reg {
                    *op = Instruction::Skip(format!("[ssa] {op}"));
                    // } else {
                    // op.as_new_move_instruction(*prev_reg, *dst);
                    // }
                }
            }
            //  else if let Some(dst) = op.target_reg_mut() {
            //     expr_tree.back_mut().unwrap().insert(expr, *dst);
            //     // We value number the assignments
            //     let m = meta.entry(Operand::Register(*dst)).or_default();
            //     let i = m.counter;
            //     m.counter += 1;
            //     m.stack.push_back(i);
            //     dst.as_phi(i);
            // }
        }
    }

    let empty = BTreeSet::new();
    let blk_label = blks[blk_idx].label.replace(':', "");

    for blk in dtree.cfg_succs_map.get(blk_label.as_str()).unwrap_or(&empty) {
        // TODO: make block -> index map
        let idx = blks.iter().position(|b| b.label.replace(':', "") == blk.as_str()).unwrap();
        let rng = phi_range(&blks[idx].instructions);

        for phi in &mut blks[idx].instructions[rng] {
            if let Instruction::Phi(r, set, ..) = phi {
                let m = meta.get_mut(&Operand::Register(*r)).unwrap();
                if m.stack.is_empty() {
                    let i = m.counter;
                    m.counter += 1;
                    m.stack.push_back(i);
                }
                let fill = m.stack.back().unwrap();
                set.insert(*fill);
            }
        }
    }

    // This is what drives the rename algorithm
    for blk in dtree.dom_succs_map.get(blk_label.as_str()).unwrap_or(&empty) {
        // TODO: make block -> index map
        let idx = blks.iter().position(|b| b.label.replace(':', "") == blk.as_str()).unwrap();
        dom_val_num(blks, idx, meta, dtree, expr_tree);
    }

    for op in &blks[blk_idx].instructions {
        if let Some(dst) = op.target_reg().map(Reg::as_register) {
            if let Some(meta) = meta.get_mut(&Operand::Register(dst)) {
                meta.stack.pop_back();
            }
        }
    }
    expr_tree.pop_back();
}
