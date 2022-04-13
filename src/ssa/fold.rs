use std::collections::{HashMap, HashSet, VecDeque};

use crate::iloc::{Function, Instruction, Reg, Val};

fn eval_cond_branch(
    expr: &Instruction,
    const_map: &HashMap<Reg, ((usize, usize), ValueKind)>,
) -> Option<Instruction> {
    let (l, r) = expr.operands();
    match (
        l.as_ref().and_then(|reg| reg.opt_reg()).and_then(|l| const_map.get(&l).map(|(_, c)| c)),
        r.as_ref().and_then(|reg| reg.opt_reg()).and_then(|r| const_map.get(&r).map(|(_, c)| c)),
    ) {
        (Some(ValueKind::Known(a)), Some(ValueKind::Known(b))) => match expr {
            Instruction::CbrEQ { loc, .. } => {
                let should_jump = a.cmp_eq(b)?.is_one();
                Some(if should_jump {
                    Instruction::ImmJump(loc.clone())
                } else {
                    Instruction::Skip(format!("{}", expr))
                })
            }
            Instruction::CbrNE { loc, .. } => {
                let should_jump = a.cmp_ne(b)?.is_one();
                Some(if should_jump {
                    Instruction::ImmJump(loc.clone())
                } else {
                    Instruction::Skip(format!("{}", expr))
                })
            }
            Instruction::CbrGT { loc, .. } => {
                let should_jump = a.cmp_gt(b)?.is_one();
                Some(if should_jump {
                    Instruction::ImmJump(loc.clone())
                } else {
                    Instruction::Skip(format!("{}", expr))
                })
            }
            Instruction::CbrGE { loc, .. } => {
                let should_jump = a.cmp_ge(b)?.is_one();
                Some(if should_jump {
                    Instruction::ImmJump(loc.clone())
                } else {
                    Instruction::Skip(format!("{}", expr))
                })
            }
            Instruction::CbrLT { loc, .. } => {
                let should_jump = a.cmp_lt(b)?.is_one();
                Some(if should_jump {
                    Instruction::ImmJump(loc.clone())
                } else {
                    Instruction::Skip(format!("{}", expr))
                })
            }
            Instruction::CbrLE { loc, .. } => {
                let should_jump = a.cmp_le(b)?.is_one();
                Some(if should_jump {
                    Instruction::ImmJump(loc.clone())
                } else {
                    Instruction::Skip(format!("{}", expr))
                })
            }
            _ => None,
        },
        (Some(ValueKind::Known(val)), None) | (None, Some(ValueKind::Known(val))) => match expr {
            Instruction::CbrT { loc, .. } => {
                let should_jump = val.is_one();
                Some(if should_jump {
                    Instruction::ImmJump(loc.clone())
                } else {
                    Instruction::Skip(format!("{}", expr))
                })
            }
            Instruction::CbrF { loc, .. } => {
                let should_jump = val.is_zero();
                Some(if should_jump {
                    Instruction::ImmJump(loc.clone())
                } else {
                    Instruction::Skip(format!("{}", expr))
                })
            }
            _ => None,
        },
        _ => None,
    }
}

fn eval_instruction(
    expr: &Instruction,
    const_map: &HashMap<Reg, ((usize, usize), ValueKind)>,
) -> Option<(ValueKind, Instruction)> {
    let (l, r) = expr.operands();
    let dst = expr.target_reg();
    match (
        l.as_ref().and_then(|reg| reg.opt_reg()).and_then(|l| const_map.get(&l).map(|(_, c)| c)),
        r.as_ref().and_then(|reg| reg.opt_reg()).and_then(|r| const_map.get(&r).map(|(_, c)| c)),
        dst,
    ) {
        // EXPRESSION REGISTERS
        // Some operation +,-,*,/,>>,etc
        (Some(n_val), Some(m_val), Some(dst)) => {
            // Can we fold this
            match (n_val, m_val) {
                (ValueKind::Known(l), ValueKind::Known(r)) => expr.fold(l, r).map(|folded| {
                    (ValueKind::Known(folded.operands().0.unwrap().clone_to_value()), folded)
                }),
                (ValueKind::Known(c), ValueKind::Maybe) => {
                    if let Some(id) = expr.identity_with_const_prop_left(c) {
                        // modify instruction with a move
                        Some((ValueKind::Maybe, expr.as_new_move_instruction(*id, *dst)?))
                    } else if matches!(expr, Instruction::Mult { .. } | Instruction::FMult { .. })
                        && c.is_zero()
                    {
                        Some((
                            ValueKind::Known(Val::Integer(0)),
                            Instruction::ImmLoad { src: Val::Integer(0), dst: *dst },
                        ))
                    } else {
                        Some((ValueKind::Maybe, expr.as_immediate_instruction_left(c)?))
                    }
                }
                (ValueKind::Maybe, ValueKind::Known(c)) => {
                    if let Some(id) = expr.identity_with_const_prop_right(c) {
                        // modify instruction with a move
                        Some((ValueKind::Maybe, expr.as_new_move_instruction(*id, *dst)?))
                    } else if matches!(expr, Instruction::Mult { .. } | Instruction::FMult { .. })
                        && c.is_zero()
                    {
                        Some((
                            ValueKind::Known(Val::Integer(0)),
                            Instruction::ImmLoad { src: Val::Integer(0), dst: *dst },
                        ))
                    } else {
                        Some((ValueKind::Maybe, expr.as_immediate_instruction_right(c)?))
                    }
                }
                _ => {
                    // Is this instruction identity
                    // This catches things like:
                    // `addI %vr3, 0 => %vr8`
                    expr.identity_register().and_then(|id| {
                        Some((ValueKind::Maybe, expr.as_new_move_instruction(id, *dst)?))
                    })
                }
            }
        }
        // This is basically a move/copy
        (Some(val), None, Some(_)) => {
            // TODO: this may do nothing..
            match val {
                ValueKind::Known(a) => {
                    Some((ValueKind::Known(a.clone()), expr.fold_two_address(a.clone())?))
                }
                _ => None,
            }
        }
        (None, Some(val), Some(_)) => {
            // TODO: this may do nothing..
            match val {
                ValueKind::Known(a) => {
                    Some((ValueKind::Known(a.clone()), expr.fold_two_address(a.clone())?))
                }
                _ => None,
            }
        }
        // Jumps, rets, push, and I/O instructions
        (Some(_src), None, None) => None,
        (None, None, Some(_)) => None,
        // No operands or target
        (None, None, None) => None,
        // All other combinations are invalid
        wtf => unreachable!("{:?} {:?}", expr, wtf),
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ValueKind {
    /// T = maybe knowable (phi, or unknown)
    Maybe,
    /// C = constant
    Known(Val),
    /// ⊥ = unknowable, because a const register has been reassigned.
    Unknowable,
}

#[derive(Debug, Default)]
pub struct ConstMap {
    /// Register to a set of block index, instruction index.
    use_to_inst: HashMap<Reg, HashSet<(usize, usize)>>,
    defined: HashMap<Reg, ((usize, usize), ValueKind)>,
}

impl ConstMap {
    pub fn add_def(&mut self, reg: Reg, val: ValueKind, blk_inst: (usize, usize)) {
        match &val {
            ValueKind::Maybe => {
                // TODO: is T ∧ T = ⊥
                self.defined.insert(reg, (blk_inst, val));
            }
            curr @ ValueKind::Known(..) => {
                match self.defined.entry(reg).or_insert_with(|| (blk_inst, val.clone())) {
                    // T ∧ x = x  ∀x
                    (_, old @ ValueKind::Maybe) => {
                        *old = val;
                    }
                    // ci ∧ cj = ⊥ if ci != cj
                    (_, old @ ValueKind::Known(..)) if &*old != curr => {
                        *old = ValueKind::Unknowable
                    }
                    // ci ∧ cj = ci if ci = cj
                    _ => {}
                }
            }
            // ⊥ ∧ x = ⊥  ∀x
            ValueKind::Unknowable => {
                self.defined.insert(reg, (blk_inst, val));
            }
        }
    }

    pub fn add_use(&mut self, reg: Reg, blk_idx: usize, inst_idx: usize) {
        self.use_to_inst.entry(reg).or_default().insert((blk_idx, inst_idx));
    }
}

pub struct WorkStuff {
    register: Reg,
    block_inst: (usize, usize),
}

impl WorkStuff {
    pub fn new(register: Reg, block: usize, instr: usize) -> Self {
        Self { register, block_inst: (block, instr) }
    }
}

pub fn const_fold(
    worklist: &mut VecDeque<WorkStuff>,
    const_vals: &mut ConstMap,
    func: &mut Function,
) {
    while let Some(WorkStuff { register: n_reg, block_inst: (n_blk, n_inst), .. }) =
        worklist.pop_front()
    {
        // TODO: not great cloning this whole use_to_inst map...
        for (blk, inst) in const_vals.use_to_inst.get(&n_reg).cloned().unwrap_or_default() {
            // If this instruction has a destination
            let Some(m) = func.blocks[blk].instructions[inst].target_reg().copied() else {
                // Else it's a possible jump/branch and the destination is a label
                let Some(folded) = eval_cond_branch(&func.blocks[blk].instructions[inst], &const_vals.defined) else {
                    continue;
                };
                if matches!(folded, Instruction::ImmJump(_)) {
                    for missed in &mut func.blocks[blk].instructions[(inst + 1)..] {
                        *missed = Instruction::Skip(format!("[ssabf] {}", missed))
                    }
                }
                func.blocks[blk].instructions[inst] = folded;

                continue;
            };
            let ((mb, mi), m_val) =
                const_vals.defined.entry(m).or_insert(((blk, inst), ValueKind::Maybe)).clone();
            if !matches!(m_val, ValueKind::Unknowable) {
                let Some((new, folded)) =
                    eval_instruction(&func.blocks[mb].instructions[mi], &const_vals.defined) else {
                        continue;
                    };

                const_vals.add_def(m, new.clone(), (mb, mi));

                func.blocks[n_blk].instructions[n_inst] = Instruction::Skip(format!(
                    "[ssacf] {}",
                    func.blocks[n_blk].instructions[n_inst]
                ));

                func.blocks[mb].instructions[mi] = folded;

                if m_val != new {
                    worklist.push_back(WorkStuff::new(m, blk, inst));
                }
            }
        }
    }
}
