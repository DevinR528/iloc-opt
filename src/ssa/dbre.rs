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
    stack: VecDeque<usize>,
}
impl Default for RenameMeta {
    fn default() -> Self {
        Self { stack: VecDeque::from([]) }
    }
}

fn new_name(reg: &Reg, dst: &mut Option<usize>, meta: &mut HashMap<Operand, RenameMeta>) {
    let m = meta.get_mut(&Operand::Register(*reg)).unwrap();
    let i = *m.stack.back().unwrap();
    m.stack.push_back(i + 1);
    *dst = Some(i);
}
fn rewrite_name(reg: &mut Reg, meta: &RenameMeta) {
    // `unwrap_or_default` is ok here since we want a zero if the stack
    // is empty
    let phi_id = meta.stack.back().copied().unwrap_or_default();
    reg.as_phi(phi_id);
}
fn phi_range(insts: &[Instruction]) -> Range<usize> {
    let start = match insts {
        [Instruction::Frame { .. }, Instruction::Label(..), Instruction::Phi(..), ..] => 2,
        [Instruction::Label(..), Instruction::Phi(..), ..] => 1,
        _ => return 0..0,
    };
    start..(start + insts.iter().skip(start).take_while(|i| i.is_phi()).count())
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
        // Only when we are actually in the block that contains the phi do we set the subscript for
        // that phi
        if let Instruction::Phi(r, set, dst) = phi {
            let m = meta.entry(Operand::Register(*r)).or_default();
            if let Some(i) = m.stack.back() {
                let new_val = *i + 1;
                dst.replace(new_val);
                m.stack.push_back(new_val);
                set.insert(new_val);
            } else {
                m.stack.push_back(0);
                set.insert(0);
            }
        }
    }
    expr_tree.push_back(HashMap::new());

    // Remove redundant/meaningless phi instructions
    for phi in &mut blks[blk_idx].instructions[rng] {
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

    // We need to iter all instructions (the frame instruction was being skipped) so don't use the
    // phi range end as a start
    for op in &mut blks[blk_idx].instructions {
        if let Instruction::Phi(..) = op {
            continue;
        }

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

        // Rename registers that don't fit neatly into the operands category
        match op {
            Instruction::Call { args, .. }
            | Instruction::Frame { params: args, .. }
            | Instruction::ImmCall { args, .. }
            | Instruction::ImmRCall { args, .. } => {
                for arg in args {
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

        if let (Some(a), b) = op.operands() {
            let expr = (a.clone(), b.clone(), op.inst_name().to_string());
            // TODO: if expr can be simplified to expr' then replace assign with `x <- expr'`

            if let Some(prev_reg) = expr_tree.iter().find_map(|map| map.get(&expr)) {
                if !op.is_tmp_expr() || op.is_call_instruction() || ssa {
                    continue;
                }

                if let Some(dst) = op.target_reg() {
                    if dst == prev_reg {
                        *op = Instruction::Skip(format!("[ssadbre] {op}"));
                    } else {
                        op.as_new_move_instruction(*prev_reg, *dst);
                    }
                }
            } else if let Some(dst) = op.target_reg_mut() {
                //
                let m = meta.entry(Operand::Register(*dst)).or_default();
                if let Some(i) = m.stack.back() {
                    let new_val = *i + 1;
                    m.stack.push_back(new_val);
                    dst.as_phi(new_val);
                } else {
                    m.stack.push_back(0);
                    dst.as_phi(0);
                }
            }
        }
    }

    let empty = BTreeSet::new();
    let blk_label = blks[blk_idx].label.replace(':', "");

    for blk in dtree.cfg_succs_map.get(blk_label.as_str()).unwrap_or(&empty) {
        // TODO: make block -> index map
        let idx = blks.iter().position(|b| b.label.starts_with(blk.as_str())).unwrap();
        let rng = phi_range(&blks[idx].instructions);
        let lab = blks[idx].label.clone();

        for phi in &mut blks[idx].instructions[rng] {
            if let Instruction::Phi(r, set, dst) = phi {
                let m = meta.get_mut(&Operand::Register(*r)).unwrap();
                // println!("child {:?}", (blk, &lab, &r, &m));

                // TODO: this is wrong for sets maybe not the subs
                if let Some(&i) = m.stack.back() {
                    set.insert(i);
                } else {
                    m.stack.push_back(0);
                    set.insert(0);
                }
            }
        }
    }

    // This is what drives the rename algorithm
    for blk in dtree.dom_tree.get(blk_label.as_str()).unwrap_or(&empty) {
        // TODO: make block -> index map
        let idx = blks.iter().position(|b| b.label.starts_with(blk.as_str())).unwrap();
        dom_val_num(blks, idx, meta, dtree, expr_tree);
    }

    for op in &blks[blk_idx].instructions {
        if let Some(dst) = op.target_reg() {
            if let Some(meta) = meta.get_mut(&Operand::Register(*dst)) {
                meta.stack.pop_back();
            }
        }
    }
    expr_tree.pop_back();
}
