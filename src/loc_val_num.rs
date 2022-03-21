use std::collections::{HashMap, HashSet};

use crate::iloc::{Block, Instruction, Loc, Operand, Reg, Val};

pub fn number_basic_block(blk: &Block) -> Option<Vec<Instruction>> {
    let mut transformed_block = false;

    // A set of all the register (destinations) that are kept, after some kind of fold/redundancy
    // elimination, due to a move
    let mut special = HashSet::new();
    let mut expr_map: HashMap<_, Reg> = HashMap::new();
    let mut const_map: HashMap<Operand, Val> = HashMap::new();

    let mut new_instr = blk.instructions.clone();
    for (idx, expr) in blk.instructions.iter().enumerate() {
        if expr.is_call_instruction() {
            // TODO: this is not OK, the input doesn't exercise it enough...
            // expr_map.clear();
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

                            special.insert(*dst);
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

                            special.insert(*dst);
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

                            special.insert(*dst);
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
                            new_instr[idx] =
                                Instruction::Skip(format!("[lvn ==] {}", new_instr[idx]));
                            continue;
                        }

                        special.insert(*value);
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
                            new_instr[idx] =
                                Instruction::Skip(format!("[lvn ==] {}", new_instr[idx]));
                            continue;
                        }

                        special.insert(*dst);
                        // modify instruction with a move
                        new_instr[idx] = expr.as_new_move_instruction(*value, *dst);
                    }
                    _ => {}
                }

                expr_map.insert((a, b, new_instr[idx].inst_name()), *dst);
            }
            // Jumps, rets, push, and I/O instructions
            (Some(_src), None, None) => {}
            // Conditional branch with (cbr_GT, etc)
            (Some(_a), Some(_b), None) => {}
            // No operands or target
            (None, None, None) => {}
            // All other combinations are invalid
            _ => unreachable!("{:?}", expr),
        }
    }

    let skips = track_used(&new_instr);
    for idx in skips {
        if new_instr[idx]
            .target_reg()
            .map_or(false, |r| const_map.contains_key(&Operand::Register(*r)))
            || new_instr[idx].is_load_imm()
        {
            transformed_block |= true;
            new_instr[idx] = Instruction::Skip(format!("[lvn unused] {}", new_instr[idx]));
        }
    }

    transformed_block |= compress_conditional_branches(&mut new_instr);
    transformed_block |= compress_load_stores(&mut new_instr, &special);

    // if then -> Some(instructions)
    transformed_block.then(|| new_instr)
}

fn track_used(instructions: &[Instruction]) -> Vec<usize> {
    let mut used_reg = HashSet::new();
    let mut live_vars = HashSet::new();
    let mut indexes = vec![];
    for (idx, expr) in instructions.iter().enumerate().rev() {
        let (l, r) = expr.operands();
        let dst = expr.target_reg();

        // Don't modify any memory operations
        if expr.is_store() {
            for op in l.iter().chain(r.iter()) {
                used_reg.insert(op.clone());
            }
            continue;
        }

        if let Some(dst) = dst {
            if live_vars.contains(dst) {
                continue;
            }
        }
        match expr {
            Instruction::I2I { src, .. } | Instruction::I2F { src, .. } => {
                if let Some(dst) = dst {
                    live_vars.insert(dst);
                }
                used_reg.insert(Operand::Register(*src));
                continue;
            }
            Instruction::ImmLoad { src: Val::Location(_), .. } => continue,
            Instruction::Call { args, .. } | Instruction::ImmCall { args, .. } => {
                for arg in args {
                    used_reg.insert(Operand::Register(*arg));
                }
            }
            _ => (),
        }

        match (l, r, dst) {
            (Some(left), Some(right), Some(_dst)) => {
                if matches!(left, Operand::Register(..)) {
                    used_reg.insert(left);
                }
                if matches!(right, Operand::Register(..)) {
                    used_reg.insert(right);
                }
            }
            (Some(src), None, Some(_dst)) => {
                if matches!(src, Operand::Register(..)) {
                    used_reg.insert(src);
                }
            }
            // Jumps, rets, push, and I/O instructions
            (Some(src), None, None) => {
                if matches!(src, Operand::Register(..)) {
                    used_reg.insert(src);
                }
                // There is no register to remove so continue
                continue;
            }
            // Conditional branch with (cbr_GT, etc)
            (Some(right), Some(left), None) => {
                if matches!(left, Operand::Register(..)) {
                    used_reg.insert(left);
                }
                if matches!(right, Operand::Register(..)) {
                    used_reg.insert(right);
                }
                continue;
            }
            // Call expressions with return can have this
            (None, None, Some(..)) => {
                continue;
            }
            // No operands or target
            (None, None, None) => {
                continue;
            }
            // All other combinations are invalid
            expr => unreachable!("{:?}", expr),
        }

        let dst = dst.unwrap();
        if !used_reg.remove(&Operand::Register(*dst)) {
            indexes.push(idx);
        }
    }

    indexes
}

fn compress_conditional_branches(instructions: &mut [Instruction]) -> bool {
    let mut modified = false;
    // We subtract 2 since we are using windows of 3 instructions to test for comparisons
    let len = instructions.len().saturating_sub(2);
    for idx in 0..len {
        if is_cond_branch(idx, instructions) {
            let (a, b) = instructions[idx].operands();
            let a = a.unwrap().copy_to_register();
            let b = b.unwrap().copy_to_register();
            // This is `test* %vr3 => %vr4`
            let test = &instructions[idx + 1];
            // This is `cbrne/cbr %vr3 -> .L0`
            let branch = &instructions[idx + 2];
            let new_instruction = if matches!(branch, Instruction::CbrT { .. }) {
                match test {
                    Instruction::TestEQ { .. } => Instruction::CbrEQ {
                        a,
                        b,
                        loc: Loc(branch.uses_label().unwrap().to_string()),
                    },
                    Instruction::TestNE { .. } => Instruction::CbrNE {
                        a,
                        b,
                        loc: Loc(branch.uses_label().unwrap().to_string()),
                    },
                    Instruction::TestGE { .. } => Instruction::CbrGE {
                        a,
                        b,
                        loc: Loc(branch.uses_label().unwrap().to_string()),
                    },
                    Instruction::TestGT { .. } => Instruction::CbrGT {
                        a,
                        b,
                        loc: Loc(branch.uses_label().unwrap().to_string()),
                    },
                    Instruction::TestLE { .. } => Instruction::CbrLE {
                        a,
                        b,
                        loc: Loc(branch.uses_label().unwrap().to_string()),
                    },
                    Instruction::TestLT { .. } => Instruction::CbrLT {
                        a,
                        b,
                        loc: Loc(branch.uses_label().unwrap().to_string()),
                    },
                    _ => unreachable!(),
                }
            } else {
                match test {
                    Instruction::TestEQ { .. } => Instruction::CbrNE {
                        a,
                        b,
                        loc: Loc(branch.uses_label().unwrap().to_string()),
                    },
                    Instruction::TestNE { .. } => Instruction::CbrEQ {
                        a,
                        b,
                        loc: Loc(branch.uses_label().unwrap().to_string()),
                    },
                    Instruction::TestGE { .. } => Instruction::CbrLT {
                        a,
                        b,
                        loc: Loc(branch.uses_label().unwrap().to_string()),
                    },
                    Instruction::TestGT { .. } => Instruction::CbrLE {
                        a,
                        b,
                        loc: Loc(branch.uses_label().unwrap().to_string()),
                    },
                    Instruction::TestLE { .. } => Instruction::CbrGT {
                        a,
                        b,
                        loc: Loc(branch.uses_label().unwrap().to_string()),
                    },
                    Instruction::TestLT { .. } => Instruction::CbrGE {
                        a,
                        b,
                        loc: Loc(branch.uses_label().unwrap().to_string()),
                    },
                    _ => unreachable!(),
                }
            };

            instructions[idx] = Instruction::Skip(format!("[lvn cbc] {}", instructions[idx]));
            instructions[idx + 1] =
                Instruction::Skip(format!("[lvn cbc] {}", instructions[idx + 1]));
            instructions[idx + 2] = new_instruction;
            modified = true;
        }
    }
    modified
}

fn is_cond_branch(idx: usize, insts: &[Instruction]) -> bool {
    matches!(
        (&insts[idx], &insts[idx + 1], &insts[idx + 2]),
        (
            Instruction::Comp { .. },
            Instruction::TestEQ { .. }
                | Instruction::TestNE { .. }
                | Instruction::TestGE { .. }
                | Instruction::TestGT { .. }
                | Instruction::TestLE { .. }
                | Instruction::TestLT { .. },
            Instruction::CbrT { .. } | Instruction::CbrF { .. }
        )
    )
}

fn compress_load_stores(instructions: &mut [Instruction], special: &HashSet<Reg>) -> bool {
    // panic!("{:?}", special);
    let mut modified = false;
    // We subtract 2 since we are using windows of 3 instructions to test for comparisons
    let len = instructions.len().saturating_sub(2);
    for idx in 0..len {
        let new_instruction = match (&instructions[idx], &instructions[idx + 1]) {
            (
                Instruction::Add { src_a: sub_src_a, src_b: sub_src_b, dst: add_dst },
                Instruction::Load { src: load_src, dst: load_dst },
            ) if add_dst == load_src => {
                Instruction::LoadAdd { src: *sub_src_a, add: *sub_src_b, dst: *load_dst }
            }
            (
                Instruction::ImmSub { src: sub_src, konst, dst: sub_dst },
                Instruction::Load { src: load_src, dst: load_dst },
            ) if sub_dst == load_src => Instruction::LoadAddImm {
                src: *sub_src,
                add: konst.negate().unwrap(),
                dst: *load_dst,
            },
            (
                Instruction::Add { src_a: add_src_a, src_b: add_src_b, dst: add_dst },
                Instruction::Store { src: store_src, dst: store_dst },
            ) if add_dst == store_dst => {
                Instruction::StoreAdd { src: *store_src, add: *add_src_b, dst: *add_src_a }
            }
            (
                Instruction::ImmSub { src: sub_src, konst, dst: sub_dst },
                Instruction::Store { src: store_src, dst: store_dst },
            ) if sub_dst == store_dst && !special.contains(sub_dst) => Instruction::StoreAddImm {
                src: *store_src,
                add: konst.negate().unwrap(),
                dst: *sub_src,
            },
            _ => continue,
        };

        instructions[idx] = Instruction::Skip(format!("[lvn l/s] {}", instructions[idx]));
        instructions[idx + 1] = new_instruction;
        modified = true;
    }
    modified
}
