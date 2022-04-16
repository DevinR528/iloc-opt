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
    fn default() -> Self { Self { stack: VecDeque::from([]) } }
}

fn rewrite_name(reg: &mut Reg, meta: &RenameMeta) {
    // `unwrap_or_default` is ok here since we want a zero if the stack
    // is empty
    let phi_id = meta.stack.back().copied().unwrap_or_default();
    reg.as_phi(phi_id);
}

pub type ScopedExprTree = VecDeque<HashMap<(Operand, Option<Operand>, String), usize>>;

pub fn dom_val_num(
    blks: &mut [Block],
    blk_idx: usize,
    meta: &mut HashMap<Reg, RenameMeta>,
    dtree: &DominatorTree,
    expr_tree: &mut ScopedExprTree,
) {
    let blk_label = blks[blk_idx].label.clone();

    expr_tree.push_back(HashMap::new());
    // println!("{blk_label} == {:?}", expr_tree);

    let mut dead = BTreeSet::new();
    // We need to iter all instructions (the frame instruction was being skipped) so don't
    // use the phi range end as a start
    for (inst_idx, op) in blks[blk_idx].instructions.iter_mut().enumerate() {
        // Remove redundant/meaningless phi instructions
        if let Instruction::Phi(r, set, subscript) = op {
            // We need to update the phi before we check it, Carr does this but all papers
            // say
            let m = meta.entry(*r).or_default();
            if let Some(i) = m.stack.back() {
                let new_val = *i + 1;
                m.stack.push_back(new_val);
            } else {
                m.stack.push_back(0);
            }
            // No more processing for Phi nodes
            continue;
        }

        let (mut a, mut b) = op.operands_mut();
        if let Some((a, meta)) = a.as_mut().map(|reg| {
            let cpy = **reg;
            (reg, meta.entry(cpy).or_default())
        }) {
            rewrite_name(a, meta);
        }
        if let Some((b, meta)) = b.as_mut().map(|reg| {
            let cpy = **reg;
            (reg, meta.entry(cpy).or_default())
        }) {
            rewrite_name(b, meta);
        }

        // Rename registers that don't fit neatly into the operands category
        match op {
            Instruction::Call { args, .. } | Instruction::Frame { params: args, .. } => {
                for arg in args {
                    let m = meta.entry(*arg).or_default();
                    rewrite_name(arg, m);
                }
            }
            Instruction::ImmCall { args, ret, .. } | Instruction::ImmRCall { args, ret, .. } => {
                for arg in args {
                    let m = meta.entry(*arg).or_default();
                    rewrite_name(arg, m);
                }
            }
            Instruction::Store { dst, .. }
            | Instruction::StoreAdd { dst, .. }
            | Instruction::StoreAddImm { dst, .. } => {
                let m = meta.entry(*dst).or_default();
                rewrite_name(dst, m);
            }
            _ => {}
        }

        if let (Some(a), b) = op.operands() {
            let is_expr = op.is_tmp_expr();
            let is_commutative = op.is_commutative();
            let inst_name = op.inst_name().to_string();
            let expr = (a.clone(), b.clone(), inst_name.clone());

            if let Some(subs) = expr_tree.iter().rev().find_map(|map| map.get(&expr)) {
                if !is_expr || op.is_call_instruction() {
                    // We need all registers to be converted
                    if let Some(dst) = op.target_reg_mut() {
                        // When we see a new definition of a register we increment it's phi value
                        let m = meta.entry(*dst).or_default();
                        if let Some(i) = m.stack.back() {
                            let new_val = *i + 1;
                            m.stack.push_back(new_val);
                        } else {
                            m.stack.push_back(0);
                        }
                    }
                    continue;
                }

                if let Some(dst) = op.target_reg_mut() {
                    // If the expression has been seen before and is equivalently ssa
                    // numbered we know it is an equal expression so we can reuse the
                    // ssa value number for this dst register

                    // PUSH(v, VN[x])
                    let m = meta.entry(*dst).or_default();
                    m.stack.push_back(*subs);
                    dead.insert(inst_idx);
                }

            } else if let Some(dst) = op.target_reg_mut() {
                // When we see a new definition of a register we increment it's phi value
                let m = meta.entry(*dst).or_default();
                if let Some(i) = m.stack.back() {
                    let new_val = *i + 1;
                    m.stack.push_back(new_val);
                } else {
                    m.stack.push_back(0);
                }

                if is_expr {
                    let expr_tree = expr_tree.back_mut().unwrap();
                    expr_tree.insert(expr, *m.stack.back().unwrap());

                    if is_commutative {
                        expr_tree.insert(
                            (b.clone().unwrap(), Some(a.clone()), inst_name),
                            *m.stack.back().unwrap(),
                        );
                    }
                }
            }
        // Non-ssa expression instruction
        // There are a few instructions that have no operands but have registers
        } else if let Some(dst) = op.target_reg_mut() {
            // When we see a new definition of a register we increment it's phi value
            let m = meta.entry(*dst).or_default();
            if let Some(i) = m.stack.back() {
                let new_val = *i + 1;
                m.stack.push_back(new_val);
            } else {
                m.stack.push_back(0);
            }
        }
    }

    let empty = BTreeSet::new();

    for blk in dtree.cfg_succs_map.get(blk_label.as_str()).unwrap_or(&empty) {

        // TODO: make block -> index map
        let idx = blks.iter().position(|b| b.label == blk.as_str()).unwrap();
        for phi in &mut blks[idx].instructions {
            if let Instruction::Phi(r, set, subscript) = phi {
                // When looking forward into successor blocks we transfer the current phi
                // number since we know this is the correct number to cross the block
                //
                // We are adding the number to the set of incoming subscripts that makes
                // up the phi
                let m = meta.entry(*r).or_default();
                if let Some(&i) = m.stack.back() {
                    set.insert(i);
                }
            }
        }
    }

    // This is what drives the rename algorithm
    for blk in dtree.dom_tree.get(blk_label.as_str()).unwrap_or(&empty) {
        println!("{blk_label} -> {blk}");
        // TODO: make block -> index map
        let idx = blks.iter().position(|b| b.label == blk.as_str()).unwrap();
        dom_val_num(blks, idx, meta, dtree, expr_tree);
    }

    for (i, op) in blks[blk_idx].instructions.iter_mut().enumerate().rev() {
        if let Some(dst) = op.target_reg_mut() {
            if let Some(meta) = meta.get_mut(dst) {
                let subscript = meta.stack.pop_back().unwrap_or_default();
                if dead.contains(&i) {
                    *op = Instruction::Skip(format!("[ssadbvn] {}", op));
                } else {
                    dst.as_phi(subscript);
                }
            }
        }
    }
    for op in blks[blk_idx].instructions.iter_mut() {
        if let Instruction::Phi(r, set, subs) = op {
            if let Some(meta) = meta.get_mut(r) {
                let subscript = meta.stack.pop_back().unwrap();
                // println!("{blk_label} | Phi({r}_{subscript}, {:?}) = {:?}", set, subscript);
                subs.replace( subscript);
            } else { unreachable!() }
        }
    }

    // Pop scope since we are leaving
    expr_tree.pop_back();

}
