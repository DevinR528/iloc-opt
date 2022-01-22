use std::collections::{HashMap, HashSet};

use crate::iloc::{Block, Function, IlocProgram, Instruction, Loc, Operand, Reg, Val};

pub fn number_basic_block(blk: &Block) -> Option<Vec<Instruction>> {
    let mut expr_map: HashMap<_, Reg> = HashMap::new();
    let mut const_map: HashMap<Operand, Val> = HashMap::new();

    let mut transformed_block = false;
    let mut new_instr = blk.instructions.clone();
    for (idx, expr) in blk.instructions.iter().enumerate() {
        if expr.is_call_instruction() {
            expr_map.clear();
            continue;
        }

        let (l, r) = expr.operands();
        let dst = expr.target_reg();
        match (l, r, dst) {
            // EXPRESSION REGISTERS
            // Some operation +,-,*,/,>>,etc
            (Some(left), Some(right), Some(dst)) => {
                // Can we fold this
                match (const_map.get(&left), const_map.get(&right)) {
                    (Some(l), Some(r)) => {
                        if let Some(folded) = expr.fold(l, r) {
                            transformed_block = true;

                            const_map.insert(
                                Operand::Register(*dst),
                                folded.operands().0.unwrap().clone_to_value(),
                            );
                            new_instr[idx] = folded;
                            continue;
                        }
                    }
                    (Some(c), None) => {
                        if let Some(id) = expr.identity_with_const_prop_left(c) {
                            transformed_block = true;

                            // modify instruction with a move
                            new_instr[idx] = expr.as_new_move_instruction(*id, *dst);

                            // Save that move for the block
                            let (a, b) = new_instr[idx].operands();
                            expr_map.insert((a.unwrap(), b, new_instr[idx].inst_name()), *dst);

                            continue;
                        } else if matches!(
                            expr,
                            Instruction::Mult { .. } | Instruction::FMult { .. }
                        ) && c.is_zero()
                        {
                            transformed_block = true;
                            new_instr[idx] =
                                Instruction::ImmLoad { src: Val::Integer(0), dst: *dst };

                            // Save that move for the block
                            let (a, b) = new_instr[idx].operands();
                            expr_map.insert((a.unwrap(), b, new_instr[idx].inst_name()), *dst);
                            const_map.insert(Operand::Register(*dst), Val::Integer(0));

                            continue;
                        } else if let Some(op_imm) = expr.as_immediate_instruction_left(c) {
                            transformed_block = true;
                            new_instr[idx] = op_imm;

                            // Save that move for the block
                            let (a, b) = new_instr[idx].operands();
                            expr_map.insert((a.unwrap(), b, new_instr[idx].inst_name()), *dst);

                            continue;
                        }
                    }
                    (None, Some(c)) => {
                        if let Some(id) = expr.identity_with_const_prop_right(c) {
                            transformed_block = true;

                            // modify instruction with a move
                            new_instr[idx] = expr.as_new_move_instruction(*id, *dst);

                            // Save that move for the block
                            let (a, b) = new_instr[idx].operands();
                            expr_map.insert((a.unwrap(), b, new_instr[idx].inst_name()), *dst);

                            continue;
                        } else if matches!(
                            expr,
                            Instruction::Mult { .. } | Instruction::FMult { .. }
                        ) && c.is_zero()
                        {
                            transformed_block = true;

                            new_instr[idx] =
                                Instruction::ImmLoad { src: Val::Integer(0), dst: *dst };
                            // Save that move for the block
                            let (a, b) = new_instr[idx].operands();
                            expr_map.insert((a.unwrap(), b, new_instr[idx].inst_name()), *dst);
                            const_map.insert(Operand::Register(*dst), Val::Integer(0));

                            continue;
                        } else if let Some(op_imm) = expr.as_immediate_instruction_right(c) {
                            transformed_block = true;
                            new_instr[idx] = op_imm;

                            // Save that move for the block
                            let (a, b) = new_instr[idx].operands();
                            expr_map.insert((a.unwrap(), b, new_instr[idx].inst_name()), *dst);

                            continue;
                        }
                    }
                    _ => {
                        // Is this instruction identity
                        // This catches things like:
                        // `addI %vr3, 0 => %vr8`
                        if let Some(id) = expr.identity_register() {
                            transformed_block = true;

                            // modify instruction with a move
                            new_instr[idx] = expr.as_new_move_instruction(id, *dst);
                            continue;
                        }
                    }
                }

                // Have we seen this before in this block
                match expr_map.get(&(left.clone(), Some(right.clone()), expr.inst_name())) {
                    Some(value) if !expr.is_store() => {
                        transformed_block = true;

                        // if we have what is effectively a move to self
                        // `x = x;`
                        if value == dst {
                            new_instr[idx] = Instruction::SKIP;
                            continue;
                        }

                        // modify instruction with a move
                        new_instr[idx] = expr.as_new_move_instruction(*value, *dst);
                        continue;
                    }
                    _ => {}
                }

                expr_map.insert((left.clone(), Some(right.clone()), expr.inst_name()), *dst);
                if expr.is_commutative() {
                    expr_map.insert((right, Some(left), expr.inst_name()), *dst);
                }
            }
            // USUALLY VAR REGISTERS
            // This is basically a move/copy
            (Some(src), None, Some(dst)) => {
                match expr_map.get(&(src.clone(), None, expr.inst_name())) {
                    Some(value) if !expr.is_store() => {
                        transformed_block = true;

                        // if we have what is effectively a move to self
                        // `x = x;`
                        if value == dst {
                            new_instr[idx] = Instruction::SKIP;
                            continue;
                        }

                        // modify instruction with a move
                        new_instr[idx] = expr.as_new_move_instruction(*value, *dst);
                        continue;
                    }
                    _ => {}
                }

                // TODO: this may do nothing..
                if let Some(val) = const_map.get(&src) {
                    if let Some(folded) = expr.fold_two_address(val) {
                        new_instr[idx] = folded;
                        continue;
                    }
                }

                // Keep track of all registers that are constants
                if expr.is_load_imm() {
                    const_map.insert(Operand::Register(*dst), src.clone_to_value());
                }
                expr_map.insert((src, None, expr.inst_name()), *dst);
            }
            // Jumps, rets, push, and I/O instructions
            (Some(src), None, None) => {}
            // No operands or target
            (None, None, None) => {}
            // All other combinations are invalid
            _ => unreachable!(),
        }
    }

    let skips = track_used(&new_instr);
    for idx in skips {
        if new_instr[idx]
            .target_reg()
            .map_or(false, |r| const_map.contains_key(&Operand::Register(*r)))
        {
            new_instr[idx] = Instruction::SKIP;
        }
    }

    // if then -> Some(instructions)
    transformed_block.then(|| new_instr)

    // println!("orig inst: {:?}", blk);
    // println!("values: {:?}", value_map);
    // println!("back: {:?}", back_val_map);
    // println!("expr: {:?}", expr_map);
    // println!("reduced: {:?}", reduced);
    // println!("opt inst: {:?}", new_instr);
}

pub fn track_used(instructions: &[Instruction]) -> Vec<usize> {
    let mut target_instruction_idx = HashMap::new();
    let mut target_reg = HashSet::new();
    let mut used_reg = HashSet::new();

    for (idx, expr) in instructions.iter().enumerate() {
        let (l, r) = expr.operands();
        let dst = expr.target_reg();

        // Don't modify any memory operations
        if expr.is_store() {
            for op in l.iter().chain(r.iter()).chain(dst.map(|r| Operand::Register(*r)).iter()) {
                target_reg.remove(op);
            }
            continue;
        }

        match (l, r, dst) {
            (Some(left), Some(right), Some(dst)) => {
                target_instruction_idx.insert(Operand::Register(*dst), idx);
                target_reg.insert(Operand::Register(*dst));
                used_reg.insert(left);
                used_reg.insert(right);
            }
            (Some(src), None, Some(dst)) => {
                target_instruction_idx.insert(Operand::Register(*dst), idx);
                target_reg.insert(Operand::Register(*dst));
                used_reg.insert(src);
            }
            // Jumps, rets, push, and I/O instructions
            (Some(src), None, None) => {}
            // No operands or target
            (None, None, None) => {}
            // All other combinations are invalid
            _ => unreachable!(),
        }
    }

    target_reg.difference(&used_reg).flat_map(|r| target_instruction_idx.get(r)).copied().collect()
}
