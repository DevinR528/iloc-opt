use std::collections::HashMap;

use crate::iloc::{Block, Function, IlocProgram, Instruction, Loc, Reg, Val};

pub fn number_basic_block(blk: Block) {
    let mut reduced = Vec::with_capacity(blk.instructions.len());

    let mut expr_map = HashMap::new();
    for expr in &blk.instructions {
        let (l, r) = expr.operands();
        if let Some(instr) = expr_map.get(&(l, r, expr.inst_name())) {
            reduced.push(instr.clone());
        } else {
            expr_map.insert((l, r, expr.inst_name()), expr);
        }
    }
}
