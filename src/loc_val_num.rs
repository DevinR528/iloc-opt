use std::collections::{HashMap, HashSet};

use crate::iloc::{Block, Function, IlocProgram, Instruction, Loc, Operand, Reg, Val};

/// Get or create and insert new value number for `val`.
fn get_value_number<'a>(
    lvn_id: &mut usize,
    val: Operand<'a>,
    value_map: &mut HashMap<Operand<'a>, usize>,
    back_val_map: &mut HashMap<usize, Operand<'a>>,
) -> usize {
    if let Some(l_val) = value_map.get(&val) {
        *l_val
    } else {
        let id = *lvn_id;
        *lvn_id += 1;

        value_map.insert(val, id);
        back_val_map.insert(id, val);
        id
    }
}

/// Checks if either left or right value has been assigned to since last use.
fn operands_not_mutated(
    l: &usize,
    r: &usize,
    set: &HashSet<usize>,
    used_ops: &HashSet<usize>,
) -> bool {
    !(set.contains(l) || set.contains(r)) && (used_ops.contains(l) || used_ops.contains(r))
}

fn operand_not_mutated(l: &usize, set: &HashSet<usize>, used_ops: &HashSet<usize>) -> bool {
    !set.contains(l) && used_ops.contains(l)
}

pub fn number_basic_block(mut blk: Block) -> Option<Vec<Instruction>> {
    let mut reduced = Vec::new();

    let mut lvn_id = 0;
    let mut expr_map: HashMap<_, usize> = HashMap::new();
    let mut value_map = HashMap::new();
    let mut back_val_map = HashMap::new();

    // TODO: this will never happen since each new dst/target is a new tmp for the block
    // as long as the register is an expression register
    let mut changed_dst = HashSet::new();
    let mut used_ops = HashSet::new();

    for (idx, expr) in blk.instructions.iter().enumerate() {
        let (l, r) = expr.operands();
        let dst = expr.target_reg();

        match (l, r, dst) {
            // EXPRESSION REGISTERS
            // Some operation +,-,*,/,>>,etc
            (Some(left), Some(right), Some(dst)) => {
                // Get value numbers for left and right
                let l_val = get_value_number(&mut lvn_id, left, &mut value_map, &mut back_val_map);
                let r_val = get_value_number(&mut lvn_id, right, &mut value_map, &mut back_val_map);

                if let Some(value) = expr_map.get(&(l_val, Some(r_val), expr.inst_name())) {
                    reduced.push((*back_val_map.get(value).unwrap(), idx));
                    value_map.insert(Operand::Register(dst), *value);
                    back_val_map.insert(*value, Operand::Register(dst));
                    continue;
                }

                // We used these values so if they are mutated they are not candidate's for dedup
                used_ops.extend([l_val, r_val]);

                let dst_val = get_value_number(
                    &mut lvn_id,
                    Operand::Register(dst),
                    &mut value_map,
                    &mut back_val_map,
                );
                // These values have been mutated, eliminating them from potential dedup
                changed_dst.insert(dst_val);

                expr_map.insert((l_val, Some(r_val), expr.inst_name()), dst_val);
            }
            // USUALLY VAR REGISTERS
            // This is basically a move/copy
            (Some(src), None, Some(dst)) => {
                let l_val = get_value_number(&mut lvn_id, src, &mut value_map, &mut back_val_map);

                if let Some(value) = expr_map.get(&(l_val, None, expr.inst_name())) {
                    reduced.push((*back_val_map.get(value).unwrap(), idx));
                    value_map.insert(Operand::Register(dst), *value);
                    back_val_map.insert(*value, Operand::Register(dst));
                    continue;
                }

                // if operand_not_mutated(&l_val, &changed_dst, &used_ops) {
                let dst_val = get_value_number(
                    &mut lvn_id,
                    Operand::Register(dst),
                    &mut value_map,
                    &mut back_val_map,
                );

                // Although the above is a future optimization, keeping track of each local value is needed still
                // since the target/destination can be mutated.
                changed_dst.insert(dst_val);
                used_ops.insert(l_val);

                expr_map.insert((l_val, None, expr.inst_name()), dst_val);
                // }
            }
            // Jumps, rets, push, and I/O instructions
            (Some(src), None, None) => {}
            // No operands or target
            (None, None, None) => {}
            // All other combinations are invalid
            _ => todo!(),
        }
    }

    if reduced.is_empty() {
        return None;
    }

    let mut new_instr = blk.instructions.clone();

    for (copy_prev_result_reg, idx) in &reduced {
        let inst = new_instr[*idx].inst_name();
        if inst == "store" {
            continue;
        }
        let dst = *new_instr[*idx].target_reg().unwrap();
        let src = copy_prev_result_reg.clone_to_reg();
        if src == dst {
            new_instr[*idx] = Instruction::SKIP;
            continue;
        }
        new_instr[*idx] = Instruction::I2I { src, dst }
    }

    // println!("orig inst: {:?}", blk);
    // println!("values: {:?}", value_map);
    // println!("back: {:?}", back_val_map);
    // println!("expr: {:?}", expr_map);
    // println!("reduced: {:?}", reduced);
    // println!("opt inst: {:?}", new_instr);

    Some(new_instr)
}
