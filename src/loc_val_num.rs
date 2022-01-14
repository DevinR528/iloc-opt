use std::collections::{HashMap, HashSet};

use crate::iloc::{Block, Function, IlocProgram, Instruction, Loc, Operand, Reg, Val};

pub fn number_basic_block<'a>(
    mut blk: &'a Block,
    fn_const_tmp_loads: &mut HashSet<(Operand<'a>, Reg)>,
) -> Option<Vec<Instruction>> {
    let mut expr_map: HashMap<_, Reg> = HashMap::new();

    let mut transformed_block = false;
    let mut new_instr = blk.instructions.clone();
    for (idx, expr) in blk.instructions.iter().enumerate() {
        let (l, r) = expr.operands();
        let dst = expr.target_reg();

        match (l, r, dst) {
            // EXPRESSION REGISTERS
            // Some operation +,-,*,/,>>,etc
            (Some(left), Some(right), Some(dst)) => {
                match expr_map.get(&(left, Some(right), expr.inst_name())) {
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
                    _ => (),
                }

                expr_map.insert((left, Some(right), expr.inst_name()), *dst);
            }
            // USUALLY VAR REGISTERS
            // This is basically a move/copy
            (Some(src), None, Some(dst)) => {
                match expr_map.get(&(src, None, expr.inst_name())) {
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
                    _ if fn_const_tmp_loads.contains(&(src, *dst)) => {
                        transformed_block = true;
                        new_instr[idx] = Instruction::SKIP;
                        continue;
                    }
                    _ => {}
                }

                if expr.is_load_imm() {
                    fn_const_tmp_loads.insert((src, *dst));
                }

                expr_map.insert((src, None, expr.inst_name()), *dst);
            }
            // Jumps, rets, push, and I/O instructions
            (Some(src), None, None) => {}
            // No operands or target
            (None, None, None) => {}
            // All other combinations are invalid
            _ => todo!(),
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
