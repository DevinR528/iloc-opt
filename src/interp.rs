use std::{collections::HashMap, io::BufRead};

use crate::iloc::{parse_text, Block, Function, IlocProgram, Instruction, Loc, Reg, Val};

pub struct Interpreter {
    /// The data segment of a program.
    ///
    /// Name to value.
    data: HashMap<Loc, Val>,
    /// Instructions broken up into functions and blocks.
    functions: HashMap<Loc, Vec<Instruction>>,
    /// A mapping of labels names to the index of the first instruction to execute after the label.
    label_map: HashMap<Loc, usize>,
    /// A map of register to value.
    registers: HashMap<Reg, Val>,
    /// The index of which instruction we are on within a block.
    inst_idx: usize,
    /// The function call stack.
    call_stack: Vec<(Loc, Vec<Val>)>,
    /// The index of the instruction to return to after a call returns.
    ret_idx: Vec<usize>,
}

impl Interpreter {
    pub fn new(iloc: IlocProgram) -> Self {
        let data = iloc
            .preamble
            .into_iter()
            .flat_map(|inst| match inst {
                Instruction::Global { name, size, align } => Some((Loc(name), Val::Integer(0))),
                Instruction::String { name, content } => Some((Loc(name), Val::String(content))),
                Instruction::Float { name, content } => Some((Loc(name), Val::Float(content))),
                _ => None,
            })
            .collect::<HashMap<_, _>>();

        let mut label_map = HashMap::new();
        let functions = iloc
            .functions
            .into_iter()
            .map(|func| {
                let mut instrs = vec![];
                for (idx, inst) in func.flatten_block_iter().enumerate() {
                    if let Instruction::Label(s) = inst {
                        label_map.insert(Loc(s.to_string()), idx);
                    }
                    instrs.push(inst.clone());
                }

                (Loc(func.label), instrs)
            })
            .collect();

        let call_stack = vec![(Loc("main".to_string()), vec![])];
        Self {
            data,
            functions,
            label_map,
            registers: HashMap::new(),
            inst_idx: 0,
            call_stack,
            ret_idx: vec![0],
        }
    }

    pub fn run_next_instruction(&mut self) -> bool {
        if self.call_stack.is_empty() {
            return false;
        }

        let (func, stack) = self.call_stack.last().unwrap();
        let instrs = self.functions.get(func).unwrap();

        // Skip these instructions
        match instrs[self.inst_idx] {
            Instruction::Frame { .. } | Instruction::Label(..) => self.inst_idx += 1,
            _ => {}
        }

        match &instrs[self.inst_idx] {
            Instruction::I2I { src, dst } => {
                self.registers
                    .insert(*dst, self.registers.get(src).cloned().unwrap_or(Val::Null));
            }
            Instruction::Add { src_a, src_b, dst } => {
                let a = self.registers.get(src_a).unwrap();
                let b = self.registers.get(src_b).unwrap();

                let val = a.add(b).unwrap();
                self.registers.insert(*dst, val);
            }
            Instruction::Sub { src_a, src_b, dst } => {
                let a = self.registers.get(src_a).unwrap();
                let b = self.registers.get(src_b).unwrap();

                let val = a.sub(b).unwrap();
                self.registers.insert(*dst, val);
            }
            Instruction::Mult { src_a, src_b, dst } => {
                let a = self.registers.get(src_a).unwrap();
                let b = self.registers.get(src_b).unwrap();

                let val = a.mult(b).unwrap();
                self.registers.insert(*dst, val);
            }
            Instruction::LShift { src_a, src_b, dst } => {
                let a = self.registers.get(src_a).unwrap();
                let b = self.registers.get(src_b).unwrap();

                let val = a.lshift(b).unwrap();
                self.registers.insert(*dst, val);
            }
            Instruction::RShift { src_a, src_b, dst } => {
                let a = self.registers.get(src_a).unwrap();
                let b = self.registers.get(src_b).unwrap();

                let val = a.rshift(b).unwrap();
                self.registers.insert(*dst, val);
            }
            Instruction::Mod { src_a, src_b, dst } => {
                let a = self.registers.get(src_a).unwrap();
                let b = self.registers.get(src_b).unwrap();

                let val = a.modulus(b).unwrap();
                self.registers.insert(*dst, val);
            }
            Instruction::And { src_a, src_b, dst } => {
                let a = self.registers.get(src_a).unwrap();
                let b = self.registers.get(src_b).unwrap();

                let val = a.and(b).unwrap();
                self.registers.insert(*dst, val);
            }
            Instruction::Or { src_a, src_b, dst } => {
                let a = self.registers.get(src_a).unwrap();
                let b = self.registers.get(src_b).unwrap();

                let val = a.or(b).unwrap();
                self.registers.insert(*dst, val);
            }
            Instruction::Not { src, dst } => {
                let a = self.registers.get(src).unwrap();

                if let Val::Integer(int) = a.clone() {
                    self.registers.insert(*dst, Val::Integer(!int));
                }
            }
            Instruction::ImmAdd { src, konst, dst } => {
                let a = self.registers.get(src).unwrap();

                let val = a.add(konst).unwrap();
                self.registers.insert(*dst, val);
            }
            Instruction::ImmSub { src, konst, dst } => {
                let a = self.registers.get(src).unwrap();

                let val = a.sub(konst).unwrap();
                self.registers.insert(*dst, val);
            }
            Instruction::ImmMult { src, konst, dst } => {
                let a = self.registers.get(src).unwrap();

                let val = a.mult(konst).unwrap();
                self.registers.insert(*dst, val);
            }
            Instruction::ImmLShift { src, konst, dst } => {
                let a = self.registers.get(src).unwrap();

                let val = a.lshift(konst).unwrap();
                self.registers.insert(*dst, val);
            }
            Instruction::ImmRShift { src, konst, dst } => {
                let a = self.registers.get(src).unwrap();

                let val = a.rshift(konst).unwrap();
                self.registers.insert(*dst, val);
            }
            Instruction::ImmLoad { src, dst } => {
                self.registers.insert(*dst, src.clone());
            }
            Instruction::Load { src, dst } => {
                let val = self.registers.get(src).unwrap().clone();
                self.registers.insert(*dst, val);
            }
            Instruction::LoadAddImm { src, add, dst } => todo!(),
            Instruction::LoadAdd { src, add, dst } => todo!(),
            Instruction::Store { src, dst } => todo!(),
            Instruction::StoreAddImm { src, add, dst } => todo!(),
            Instruction::StoreAdd { src, add, dst } => todo!(),
            Instruction::CmpLT { a, b, dst } => {
                let a = self.registers.get(a).unwrap();
                let b = self.registers.get(b).unwrap();
                let val = a.cmp_lt(b).unwrap();
                self.registers.insert(*dst, val);
            }
            Instruction::CmpLE { a, b, dst } => {
                let a = self.registers.get(a).unwrap();
                let b = self.registers.get(b).unwrap();
                let val = a.cmp_le(b).unwrap();
                self.registers.insert(*dst, val);
            }
            Instruction::CmpGT { a, b, dst } => {
                let a = self.registers.get(a).unwrap();
                let b = self.registers.get(b).unwrap();
                let val = a.cmp_gt(b).unwrap();
                self.registers.insert(*dst, val);
            }
            Instruction::CmpGE { a, b, dst } => {
                let a = self.registers.get(a).unwrap();
                let b = self.registers.get(b).unwrap();
                let val = a.cmp_ge(b).unwrap();
                self.registers.insert(*dst, val);
            }
            Instruction::CmpEQ { a, b, dst } => {
                let a = self.registers.get(a).unwrap();
                let b = self.registers.get(b).unwrap();
                let val = a.cmp_eq(b).unwrap();
                self.registers.insert(*dst, val);
            }
            Instruction::CmpNE { a, b, dst } => {
                let a = self.registers.get(a).unwrap();
                let b = self.registers.get(b).unwrap();
                let val = a.cmp_ne(b).unwrap();
                self.registers.insert(*dst, val);
            }
            Instruction::Comp { a, b, dst } => {
                let a = self.registers.get(a).unwrap();
                let b = self.registers.get(b).unwrap();
                let val = a.sub(b).unwrap();
                self.registers.insert(*dst, val);
            }
            Instruction::TestEQ { test, dst } => {
                let a = self.registers.get(test).unwrap();
                let is_eq = a.is_zero();
                self.registers
                    .insert(*dst, Val::Integer(if is_eq { 1 } else { 0 }));
            }
            Instruction::TestNE { test, dst } => {
                let a = self.registers.get(test).unwrap();
                let is_ne = !a.is_zero();
                self.registers
                    .insert(*dst, Val::Integer(if is_ne { 1 } else { 0 }));
            }
            Instruction::TestGT { test, dst } => {
                let a = self.registers.get(test).unwrap();
                let is_gt = match a {
                    Val::Integer(i) if *i > 0 => 1,
                    Val::Float(f) if *f > 0.0 => 1,
                    _ => 0,
                };
                self.registers.insert(*dst, Val::Integer(is_gt));
            }
            Instruction::TestGE { test, dst } => {
                let a = self.registers.get(test).unwrap();
                let is_ge = match a {
                    Val::Integer(i) if *i >= 0 => 1,
                    Val::Float(f) if *f >= 0.0 => 1,
                    _ => 0,
                };
                self.registers.insert(*dst, Val::Integer(is_ge));
            }
            Instruction::TestLT { test, dst } => {
                let a = self.registers.get(test).unwrap();
                let is_lt = match a {
                    Val::Integer(i) if *i < 0 => 1,
                    Val::Float(f) if *f < 0.0 => 1,
                    _ => 0,
                };
                self.registers.insert(*dst, Val::Integer(is_lt));
            }
            Instruction::TestLE { test, dst } => {
                let a = self.registers.get(test).unwrap();
                let is_le = match a {
                    Val::Integer(i) if *i <= 0 => 1,
                    Val::Float(f) if *f <= 0.0 => 1,
                    _ => 0,
                };
                self.registers.insert(*dst, Val::Integer(is_le));
            }
            Instruction::ImmJump(loc) => {
                let jmp_idx = self.label_map.get(loc).unwrap();
                self.inst_idx = *jmp_idx;
                return true;
            }
            Instruction::Jump(reg) => todo!(),
            Instruction::Call { name, args } => {
                self.ret_idx.push(self.inst_idx + 1);
                self.call_stack.push((Loc(name.to_owned()), vec![]));
                self.inst_idx = 0;

                return true;
            }
            Instruction::ImmCall { name, args, ret } => todo!(),
            Instruction::ImmRCall { reg, args, ret } => todo!(),
            Instruction::Ret => {
                self.inst_idx = self.ret_idx.pop().unwrap();
                self.call_stack.pop();
                return true;
            }
            Instruction::ImmRet(_) => todo!(),
            Instruction::CbrT { cond, loc } => {
                let a = self.registers.get(cond).unwrap();
                let should_jump = match a {
                    Val::Integer(i) if *i == 1 => true,
                    Val::Float(f) if *f == 1.0 => true,
                    _ => false,
                };
                if should_jump {
                    let jmp_idx = self.label_map.get(loc).unwrap();
                    self.inst_idx = *jmp_idx;
                    return true;
                }
            }
            Instruction::CbrF { cond, loc } => {
                let a = self.registers.get(cond).unwrap();
                let should_jump = match a {
                    Val::Integer(i) if *i == 1 => true,
                    Val::Float(f) if *f == 1.0 => true,
                    _ => false,
                };
                // This is conditional branch if NOT equal
                if !should_jump {
                    let jmp_idx = self.label_map.get(loc).unwrap();
                    self.inst_idx = *jmp_idx;
                    return true;
                }
            }
            Instruction::CbrLT { a, b, loc } => {
                let a = self.registers.get(a).unwrap();
                let b = self.registers.get(b).unwrap();
                let should_jump = match a.cmp_lt(b).unwrap() {
                    Val::Integer(i) if i == 1 => true,
                    Val::Float(f) if f == 1.0 => true,
                    _ => false,
                };
                if should_jump {
                    let jmp_idx = self.label_map.get(loc).unwrap();
                    self.inst_idx = *jmp_idx;
                    return true;
                }
            }
            Instruction::CbrLE { a, b, loc } => {
                let a = self.registers.get(a).unwrap();
                let b = self.registers.get(b).unwrap();
                let should_jump = match a.cmp_le(b).unwrap() {
                    Val::Integer(i) if i == 1 => true,
                    Val::Float(f) if f == 1.0 => true,
                    _ => false,
                };
                if should_jump {
                    let jmp_idx = self.label_map.get(loc).unwrap();
                    self.inst_idx = *jmp_idx;
                    return true;
                }
            }
            Instruction::CbrGT { a, b, loc } => {
                let a = self.registers.get(a).unwrap();
                let b = self.registers.get(b).unwrap();
                let should_jump = match a.cmp_gt(b).unwrap() {
                    Val::Integer(i) if i == 1 => true,
                    Val::Float(f) if f == 1.0 => true,
                    _ => false,
                };
                if should_jump {
                    let jmp_idx = self.label_map.get(loc).unwrap();
                    self.inst_idx = *jmp_idx;
                    return true;
                }
            }
            Instruction::CbrGE { a, b, loc } => {
                let a = self.registers.get(a).unwrap();
                let b = self.registers.get(b).unwrap();
                let should_jump = match a.cmp_ge(b).unwrap() {
                    Val::Integer(i) if i == 1 => true,
                    Val::Float(f) if f == 1.0 => true,
                    _ => false,
                };
                if should_jump {
                    let jmp_idx = self.label_map.get(loc).unwrap();
                    self.inst_idx = *jmp_idx;
                    return true;
                }
            }
            Instruction::CbrEQ { a, b, loc } => {
                let a = self.registers.get(a).unwrap();
                let b = self.registers.get(b).unwrap();
                let should_jump = match a.cmp_eq(b).unwrap() {
                    Val::Integer(i) if i == 1 => true,
                    Val::Float(f) if f == 1.0 => true,
                    _ => false,
                };
                if should_jump {
                    let jmp_idx = self.label_map.get(loc).unwrap();
                    self.inst_idx = *jmp_idx;
                    return true;
                }
            }
            Instruction::CbrNE { a, b, loc } => {
                let a = self.registers.get(a).unwrap();
                let b = self.registers.get(b).unwrap();
                let should_jump = match a.cmp_ne(b).unwrap() {
                    Val::Integer(i) if i == 1 => true,
                    Val::Float(f) if f == 1.0 => true,
                    _ => false,
                };
                if should_jump {
                    let jmp_idx = self.label_map.get(loc).unwrap();
                    self.inst_idx = *jmp_idx;
                    return true;
                }
            }
            Instruction::F2I { src, dst } => todo!(),
            Instruction::I2F { src, dst } => todo!(),
            Instruction::F2F { src, dst } => todo!(),
            Instruction::FAdd { src_a, src_b, dst } => {
                let a = self.registers.get(src_a).unwrap();
                let b = self.registers.get(src_b).unwrap();

                let val = a.fadd(b).unwrap();
                self.registers.insert(*dst, val);
            }
            Instruction::FSub { src_a, src_b, dst } => {
                let a = self.registers.get(src_a).unwrap();
                let b = self.registers.get(src_b).unwrap();

                let val = a.fsub(b).unwrap();
                self.registers.insert(*dst, val);
            }
            Instruction::FMult { src_a, src_b, dst } => {
                let a = self.registers.get(src_a).unwrap();
                let b = self.registers.get(src_b).unwrap();

                let val = a.fmult(b).unwrap();
                self.registers.insert(*dst, val);
            }
            Instruction::FDiv { src_a, src_b, dst } => {
                let a = self.registers.get(src_a).unwrap();
                let b = self.registers.get(src_b).unwrap();

                let val = a.fdiv(b).unwrap();
                self.registers.insert(*dst, val);
            }
            Instruction::FComp { src_a, src_b, dst } => {
                let a = self.registers.get(src_a).unwrap();
                let b = self.registers.get(src_b).unwrap();

                let val = a.fsub(b).unwrap();
                self.registers.insert(*dst, val);
            }
            Instruction::FLoad { src, dst } => todo!(),
            Instruction::FLoadAddImm { src, add, dst } => todo!(),
            Instruction::FLoadAdd { src, add, dst } => todo!(),
            Instruction::FStore { src, dst } => todo!(),
            Instruction::FStoreAddImm { src, add, dst } => todo!(),
            Instruction::FStoreAdd { src, add, dst } => todo!(),
            Instruction::FRead(r) => {
                let mut buf = String::new();
                let mut handle = std::io::stdin_locked();
                handle.read_line(&mut buf).unwrap();
                self.registers
                    .insert(*r, Val::Float(buf.parse::<f64>().unwrap()));
            }
            Instruction::IRead(r) => {
                let mut buf = String::new();
                let mut handle = std::io::stdin_locked();
                handle.read_line(&mut buf).unwrap();
                self.registers.insert(*r, Val::Float(buf.parse().unwrap()));
            }
            Instruction::FWrite(r) => println!("{:?}", self.registers.get(r)),
            Instruction::IWrite(r) => println!("{:?}", self.registers.get(r)),
            Instruction::SWrite(r) => println!("{:?}", self.registers.get(r)),
            _ => todo!("{:?}", instrs[self.inst_idx]),
        }
        self.inst_idx += 1;
        true
    }

    pub fn curr_instruction(&self) -> Option<&Instruction> {
        let (func, stack) = self.call_stack.last()?;
        let instrs = self.functions.get(func)?;
        instrs.get(self.inst_idx)
    }
}

pub fn run_interpreter(iloc: IlocProgram) -> Result<(), &'static str> {
    let mut interpreter = Interpreter::new(iloc);

    // Now we can get input from the user
    while interpreter.run_next_instruction() {
        println!("{:?}", interpreter.curr_instruction());
        let x = &mut interpreter;
    }

    Ok(())
}
