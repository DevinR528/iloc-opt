use std::collections::{HashMap, HashSet};

use crate::iloc::{Block, Function, IlocProgram, Instruction, Loc, Operand, Reg, Val};

pub fn number_basic_block(blk: &Block) -> Option<Vec<Instruction>> {
    let mut transformed_block = false;
    let mut expr_map: HashMap<_, Reg> = HashMap::new();
    let mut const_map: HashMap<Operand, Val> = HashMap::new();

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
                            new_instr[idx] = folded;

                            const_map.insert(
                                Operand::Register(*dst),
                                new_instr[idx].operands().0.unwrap().clone_to_value(),
                            );

                            continue;
                        }
                    }
                    (Some(c), None) => {
                        if let Some(id) = expr.identity_with_const_prop_left(c) {
                            transformed_block = true;

                            // modify instruction with a move
                            new_instr[idx] = expr.as_new_move_instruction(*id, *dst);
                        } else if matches!(
                            expr,
                            Instruction::Mult { .. } | Instruction::FMult { .. }
                        ) && c.is_zero()
                        {
                            transformed_block = true;
                            new_instr[idx] =
                                Instruction::ImmLoad { src: Val::Integer(0), dst: *dst };
                        } else if let Some(op_imm) = expr.as_immediate_instruction_left(c) {
                            transformed_block = true;
                            new_instr[idx] = op_imm;
                        }
                    }
                    (None, Some(c)) => {
                        if let Some(id) = expr.identity_with_const_prop_right(c) {
                            transformed_block = true;

                            // modify instruction with a move
                            new_instr[idx] = expr.as_new_move_instruction(*id, *dst);
                        } else if matches!(
                            expr,
                            Instruction::Mult { .. } | Instruction::FMult { .. }
                        ) && c.is_zero()
                        {
                            transformed_block = true;

                            new_instr[idx] =
                                Instruction::ImmLoad { src: Val::Integer(0), dst: *dst };
                        } else if let Some(op_imm) = expr.as_immediate_instruction_right(c) {
                            transformed_block = true;
                            new_instr[idx] = op_imm;
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
                        }
                    }
                }

                let (a, b) = new_instr[idx].operands();
                let a = a.unwrap();

                // Keep track of all registers that are constants
                if new_instr[idx].is_load_imm() {
                    const_map.insert(Operand::Register(*dst), a.clone_to_value());
                }

                // Have we seen this before in this block
                match expr_map.get(&(a.clone(), b.clone(), new_instr[idx].inst_name())) {
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
                    }
                    _ => {}
                }

                if new_instr[idx].is_commutative() {
                    expr_map.insert(
                        (b.clone().unwrap(), Some(a.clone()), new_instr[idx].inst_name()),
                        *dst,
                    );
                }
                expr_map.insert((a, b, new_instr[idx].inst_name()), *dst);
            }
            // USUALLY VAR REGISTERS
            // This is basically a move/copy
            (Some(src), None, Some(dst)) => {
                // TODO: this may do nothing..
                if let Some(val) = const_map.get(&src) {
                    if let Some(folded) = expr.fold_two_address(val) {
                        new_instr[idx] = folded;
                    }
                }

                let (a, b) = new_instr[idx].operands();
                let a = a.unwrap();

                // Keep track of all registers that are constants
                if new_instr[idx].is_load_imm() {
                    const_map.insert(Operand::Register(*dst), a.clone_to_value());
                }

                match expr_map.get(&(a.clone(), b.clone(), new_instr[idx].inst_name())) {
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
                    }
                    _ => {}
                }

                expr_map.insert((a, b, new_instr[idx].inst_name()), *dst);
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
            || new_instr[idx].is_load_imm()
        {
            new_instr[idx] = Instruction::SKIP;
        } else {
            // println!("{:?}", new_instr[idx]);
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
    let mut target_instruction_idx: HashMap<_, Vec<_>> = HashMap::new();
    let mut target_reg = vec![];
    let mut used_reg: HashMap<_, usize> = HashMap::new();

    for (idx, expr) in instructions.iter().enumerate() {
        let (l, r) = expr.operands();
        let dst = expr.target_reg();

        // Don't modify any memory operations
        if expr.is_store() {
            for op in l.iter().chain(r.iter()).chain(dst.map(|r| Operand::Register(*r)).iter()) {
                *used_reg.entry(op.clone()).or_insert(0) += 1;
                // if let Some(pos) = target_reg.iter().position(|reg| reg == op) {
                //     target_reg.remove(pos);
                // }
            }
            continue;
        }

        match (l, r, dst) {
            (Some(left), Some(right), Some(dst)) => {
                target_instruction_idx.entry(Operand::Register(*dst)).or_default().push(idx);
                target_reg.push(Operand::Register(*dst));

                if matches!(left, Operand::Register(..)) {
                    *used_reg.entry(left).or_insert(0) += 1;
                }
                if matches!(right, Operand::Register(..)) {
                    *used_reg.entry(right).or_insert(0) += 1;
                }
            }
            (Some(src), None, Some(dst)) => {
                target_instruction_idx.entry(Operand::Register(*dst)).or_default().push(idx);
                target_reg.push(Operand::Register(*dst));

                if matches!(src, Operand::Register(..)) {
                    *used_reg.entry(src).or_insert(0) += 1;
                }
            }
            // Jumps, rets, push, and I/O instructions
            (Some(src), None, None) => {}
            // No operands or target
            (None, None, None) => {}
            // All other combinations are invalid
            _ => unreachable!(),
        }
    }

    fn add_one(c: &mut usize) -> usize {
        *c = c.saturating_sub(1);
        *c
    }

    let mut indexes = vec![];
    for r in target_reg.iter() {
        if !used_reg.contains_key(r) {
            let idxs = target_instruction_idx.get(r).unwrap();
            indexes.extend(idxs);
            for idx in idxs {
                let (a, b) = instructions[*idx].operands();
                if let Some(a) = a {
                    used_reg.remove(&a);
                }
                if let Some(b) = b {
                    used_reg.remove(&b);
                }
            }
        }
    }
    indexes
}
