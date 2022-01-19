use std::{
    collections::{BTreeSet, HashMap, HashSet},
    io::BufRead,
    str::FromStr,
};

use crate::iloc::{parse_text, Block, Function, IlocProgram, Instruction, Loc, Reg, Val};

const STACK_SIZE: usize = 4096;

fn set_stack(stack: &mut Vec<Val>, idx: usize, val: Val) {
    stack[idx] = val;
}

pub struct Interpreter {
    /// The data segment of a program.
    ///
    /// Name to value.
    data: HashMap<Loc, Val>,
    /// Instructions broken up into functions and blocks.
    functions: HashMap<Loc, Vec<(usize, Instruction)>>,
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
        let mut preamble_lines = iloc.preamble.len();

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
                    preamble_lines += 1;
                    if let Instruction::Label(s) = inst {
                        label_map.insert(Loc(s.replace(':', "")), idx);
                    }
                    instrs.push((preamble_lines, inst.clone()));
                }

                (Loc(func.label), instrs)
            })
            .collect();

        let mut registers = HashMap::new();
        // This is the data stack pointer, in a real program it would be a pointer to the memory
        // address of the beginning of the program itself, since our stack is separate it's just the 0th
        // index of the stack
        registers.insert(Reg::Var(0), Val::Integer(STACK_SIZE as isize));

        let call_stack = vec![(Loc("main".to_string()), vec![Val::Null; STACK_SIZE])];
        Self {
            data,
            functions,
            label_map,
            registers,
            inst_idx: 0,
            call_stack,
            ret_idx: vec![0],
        }
    }

    pub fn run_next_instruction(&mut self) -> Option<bool> {
        if self.call_stack.is_empty() {
            return Some(false);
        }

        let (func, stack) = self.call_stack.last_mut().unwrap();
        let instrs = self.functions.get(func).unwrap();

        // Skip these instructions
        match instrs[self.inst_idx].1 {
            Instruction::Frame { .. } | Instruction::Label(..) => self.inst_idx += 1,
            _ => {}
        }

        match &instrs[self.inst_idx].1 {
            Instruction::I2I { src, dst } => {
                self.registers
                    .insert(*dst, self.registers.get(src).cloned()?);
            }
            Instruction::Add { src_a, src_b, dst } => {
                let a = self.registers.get(src_a)?;
                let b = self.registers.get(src_b)?;

                let val = a.add(b)?;
                self.registers.insert(*dst, val);
            }
            Instruction::Sub { src_a, src_b, dst } => {
                let a = self.registers.get(src_a)?;
                let b = self.registers.get(src_b)?;

                let val = a.sub(b)?;
                self.registers.insert(*dst, val);
            }
            Instruction::Mult { src_a, src_b, dst } => {
                let a = self.registers.get(src_a)?;
                let b = self.registers.get(src_b)?;

                let val = a.mult(b)?;
                self.registers.insert(*dst, val);
            }
            Instruction::LShift { src_a, src_b, dst } => {
                let a = self.registers.get(src_a)?;
                let b = self.registers.get(src_b)?;

                let val = a.lshift(b)?;
                self.registers.insert(*dst, val);
            }
            Instruction::RShift { src_a, src_b, dst } => {
                let a = self.registers.get(src_a)?;
                let b = self.registers.get(src_b)?;

                let val = a.rshift(b)?;
                self.registers.insert(*dst, val);
            }
            Instruction::Mod { src_a, src_b, dst } => {
                let a = self.registers.get(src_a)?;
                let b = self.registers.get(src_b)?;

                let val = a.modulus(b)?;
                self.registers.insert(*dst, val);
            }
            Instruction::And { src_a, src_b, dst } => {
                let a = self.registers.get(src_a)?;
                let b = self.registers.get(src_b)?;

                let val = a.and(b)?;
                self.registers.insert(*dst, val);
            }
            Instruction::Or { src_a, src_b, dst } => {
                let a = self.registers.get(src_a)?;
                let b = self.registers.get(src_b)?;

                let val = a.or(b)?;
                self.registers.insert(*dst, val);
            }
            Instruction::Not { src, dst } => {
                let a = self.registers.get(src)?;

                if let Val::Integer(int) = a.clone() {
                    self.registers.insert(*dst, Val::Integer(!int));
                }
            }
            Instruction::ImmAdd { src, konst, dst } => {
                let a = self.registers.get(src)?;

                let val = a.add(konst)?;
                self.registers.insert(*dst, val);
            }
            Instruction::ImmSub { src, konst, dst } => {
                let a = self.registers.get(src)?;

                let val = a.sub(konst)?;
                self.registers.insert(*dst, val);
            }
            Instruction::ImmMult { src, konst, dst } => {
                let a = self.registers.get(src)?;

                let val = a.mult(konst)?;
                self.registers.insert(*dst, val);
            }
            Instruction::ImmLShift { src, konst, dst } => {
                let a = self.registers.get(src)?;

                let val = a.lshift(konst)?;
                self.registers.insert(*dst, val);
            }
            Instruction::ImmRShift { src, konst, dst } => {
                let a = self.registers.get(src)?;

                let val = a.rshift(konst)?;
                self.registers.insert(*dst, val);
            }
            Instruction::ImmLoad { src, dst } => {
                let src = if let Val::Location(s) = src {
                    self.data.get(&Loc(s.to_owned()))?.clone()
                } else {
                    src.clone()
                };
                self.registers.insert(*dst, src);
            }
            Instruction::Load { src, dst } => {
                let stack_idx = self.registers.get(src)?;
                let val = stack[stack_idx.to_int()? as usize].clone();
                self.registers.insert(*dst, val);
            }
            Instruction::LoadAddImm { src, add, dst } => {
                let stack_idx = self.registers.get(src)?.to_int()? as usize;
                let val = stack[stack_idx + (add.to_int()? as usize)].clone();
                self.registers.insert(*dst, val);
            }
            Instruction::LoadAdd { src, add, dst } => {
                let stack_idx = self.registers.get(src)?.to_int()? as usize;
                let add = self.registers.get(add)?.to_int()? as usize;

                let val = stack[stack_idx + add].clone();
                self.registers.insert(*dst, val);
            }
            Instruction::Store { src, dst } => {
                let val = self.registers.get(src)?.clone();
                let stack_idx = self.registers.get(dst)?.to_int()? as usize;
                set_stack(stack, stack_idx, val);
            }
            Instruction::StoreAddImm { src, add, dst } => {
                let val = self.registers.get(src)?.clone();
                let stack_idx = self.registers.get(dst)?.to_int()? as usize;
                set_stack(stack, stack_idx + (add.to_int()? as usize), val);
            }
            Instruction::StoreAdd { src, add, dst } => {
                let val = self.registers.get(src)?.clone();

                let add = self.registers.get(add)?.to_int()? as usize;
                let stack_idx = self.registers.get(dst)?.to_int()? as usize;

                set_stack(stack, stack_idx + add, val);
            }
            Instruction::CmpLT { a, b, dst } => {
                let a = self.registers.get(a)?;
                let b = self.registers.get(b)?;
                let val = a.cmp_lt(b)?;
                self.registers.insert(*dst, val);
            }
            Instruction::CmpLE { a, b, dst } => {
                let a = self.registers.get(a)?;
                let b = self.registers.get(b)?;
                let val = a.cmp_le(b)?;
                self.registers.insert(*dst, val);
            }
            Instruction::CmpGT { a, b, dst } => {
                let a = self.registers.get(a)?;
                let b = self.registers.get(b)?;
                let val = a.cmp_gt(b)?;
                self.registers.insert(*dst, val);
            }
            Instruction::CmpGE { a, b, dst } => {
                let a = self.registers.get(a)?;
                let b = self.registers.get(b)?;
                let val = a.cmp_ge(b)?;
                self.registers.insert(*dst, val);
            }
            Instruction::CmpEQ { a, b, dst } => {
                let a = self.registers.get(a)?;
                let b = self.registers.get(b)?;
                let val = a.cmp_eq(b)?;
                self.registers.insert(*dst, val);
            }
            Instruction::CmpNE { a, b, dst } => {
                let a = self.registers.get(a)?;
                let b = self.registers.get(b)?;
                let val = a.cmp_ne(b)?;
                self.registers.insert(*dst, val);
            }
            Instruction::Comp { a, b, dst } => {
                let a = self.registers.get(a)?;
                let b = self.registers.get(b)?;

                let val = a.comp(b)?;
                self.registers.insert(*dst, val);
            }
            Instruction::TestEQ { test, dst } => {
                let a = self.registers.get(test)?;
                let is_eq = a.is_zero();
                self.registers
                    .insert(*dst, Val::Integer(if is_eq { 1 } else { 0 }));
            }
            Instruction::TestNE { test, dst } => {
                let a = self.registers.get(test)?;
                let is_ne = !a.is_zero();
                self.registers
                    .insert(*dst, Val::Integer(if is_ne { 1 } else { 0 }));
            }
            Instruction::TestGT { test, dst } => {
                let a = self.registers.get(test)?;
                let is_gt = match a {
                    Val::Integer(i) if *i > 0 => 1,
                    Val::Float(f) if *f > 0.0 => 1,
                    _ => 0,
                };
                self.registers.insert(*dst, Val::Integer(is_gt));
            }
            Instruction::TestGE { test, dst } => {
                let a = self.registers.get(test)?;
                let is_ge = match a {
                    Val::Integer(i) if *i >= 0 => 1,
                    Val::Float(f) if *f >= 0.0 => 1,
                    _ => 0,
                };
                self.registers.insert(*dst, Val::Integer(is_ge));
            }
            Instruction::TestLT { test, dst } => {
                let a = self.registers.get(test)?;
                let is_lt = match a {
                    Val::Integer(i) if *i < 0 => 1,
                    Val::Float(f) if *f < 0.0 => 1,
                    _ => 0,
                };
                self.registers.insert(*dst, Val::Integer(is_lt));
            }
            Instruction::TestLE { test, dst } => {
                let a = self.registers.get(test)?;
                let is_le = match a {
                    Val::Integer(i) if *i <= 0 => 1,
                    Val::Float(f) if *f <= 0.0 => 1,
                    _ => 0,
                };
                self.registers.insert(*dst, Val::Integer(is_le));
            }
            Instruction::ImmJump(loc) => {
                let jmp_idx = self.label_map.get(loc)?;
                self.inst_idx = *jmp_idx;
                return Some(true);
            }
            Instruction::Jump(reg) => todo!(),
            Instruction::Call { name, args } => {
                self.ret_idx.push(self.inst_idx + 1);
                self.call_stack
                    .push((Loc(name.to_owned()), vec![Val::Null; STACK_SIZE]));
                self.inst_idx = 0;

                return Some(true);
            }
            Instruction::ImmCall { name, args, ret } => todo!(),
            Instruction::ImmRCall { reg, args, ret } => todo!(),
            Instruction::Ret => {
                self.inst_idx = self.ret_idx.pop()?;
                self.call_stack.pop();
                return Some(true);
            }
            Instruction::ImmRet(_) => todo!(),
            Instruction::CbrT { cond, loc } => {
                let a = self.registers.get(cond)?;
                let should_jump = match a {
                    Val::Integer(i) if *i == 1 => true,
                    Val::Float(f) if *f == 1.0 => true,
                    _ => false,
                };
                if should_jump {
                    let jmp_idx = self.label_map.get(loc)?;
                    self.inst_idx = *jmp_idx;
                    return Some(true);
                }
            }
            Instruction::CbrF { cond, loc } => {
                let a = self.registers.get(cond)?;
                let should_jump = match a {
                    Val::Integer(i) if *i == 1 => true,
                    Val::Float(f) if *f == 1.0 => true,
                    _ => false,
                };
                // This is conditional branch if NOT equal
                if !should_jump {
                    let jmp_idx = self.label_map.get(loc)?;
                    self.inst_idx = *jmp_idx;
                    return Some(true);
                }
            }
            Instruction::CbrLT { a, b, loc } => {
                let a = self.registers.get(a)?;
                let b = self.registers.get(b)?;
                let should_jump = match a.cmp_lt(b)? {
                    Val::Integer(i) if i == 1 => true,
                    Val::Float(f) if f == 1.0 => true,
                    _ => false,
                };
                if should_jump {
                    let jmp_idx = self.label_map.get(loc)?;
                    self.inst_idx = *jmp_idx;
                    return Some(true);
                }
            }
            Instruction::CbrLE { a, b, loc } => {
                let a = self.registers.get(a)?;
                let b = self.registers.get(b)?;
                let should_jump = match a.cmp_le(b)? {
                    Val::Integer(i) if i == 1 => true,
                    Val::Float(f) if f == 1.0 => true,
                    _ => false,
                };
                if should_jump {
                    let jmp_idx = self.label_map.get(loc)?;
                    self.inst_idx = *jmp_idx;
                    return Some(true);
                }
            }
            Instruction::CbrGT { a, b, loc } => {
                let a = self.registers.get(a)?;
                let b = self.registers.get(b)?;
                let should_jump = match a.cmp_gt(b)? {
                    Val::Integer(i) if i == 1 => true,
                    Val::Float(f) if f == 1.0 => true,
                    _ => false,
                };
                if should_jump {
                    let jmp_idx = self.label_map.get(loc)?;
                    self.inst_idx = *jmp_idx;
                    return Some(true);
                }
            }
            Instruction::CbrGE { a, b, loc } => {
                let a = self.registers.get(a)?;
                let b = self.registers.get(b)?;
                let should_jump = match a.cmp_ge(b)? {
                    Val::Integer(i) if i == 1 => true,
                    Val::Float(f) if f == 1.0 => true,
                    _ => false,
                };
                if should_jump {
                    let jmp_idx = self.label_map.get(loc)?;
                    self.inst_idx = *jmp_idx;
                    return Some(true);
                }
            }
            Instruction::CbrEQ { a, b, loc } => {
                let a = self.registers.get(a)?;
                let b = self.registers.get(b)?;
                let should_jump = match a.cmp_eq(b)? {
                    Val::Integer(i) if i == 1 => true,
                    Val::Float(f) if f == 1.0 => true,
                    _ => false,
                };
                if should_jump {
                    let jmp_idx = self.label_map.get(loc)?;
                    self.inst_idx = *jmp_idx;
                    return Some(true);
                }
            }
            Instruction::CbrNE { a, b, loc } => {
                let a = self.registers.get(a)?;
                let b = self.registers.get(b)?;
                let should_jump = match a.cmp_ne(b)? {
                    Val::Integer(i) if i == 1 => true,
                    Val::Float(f) if f == 1.0 => true,
                    _ => false,
                };
                if should_jump {
                    let jmp_idx = self.label_map.get(loc)?;
                    self.inst_idx = *jmp_idx;
                    return Some(true);
                }
            }
            Instruction::F2I { src, dst } => {
                let int_from_float = if let Val::Float(f) = self.registers.get(src).cloned()? {
                    unsafe { f.to_int_unchecked::<isize>() }
                } else {
                    todo!("float error")
                };
                self.registers.insert(*dst, Val::Integer(int_from_float));
            }
            Instruction::I2F { src, dst } => {
                let float_from_int = if let Val::Integer(i) = self.registers.get(src).cloned()? {
                    i as f64
                } else {
                    todo!("integer error")
                };
                self.registers.insert(*dst, Val::Float(float_from_int));
            }
            Instruction::F2F { src, dst } => {
                self.registers
                    .insert(*dst, self.registers.get(src).cloned()?);
            }
            Instruction::FAdd { src_a, src_b, dst } => {
                let a = self.registers.get(src_a)?;
                let b = self.registers.get(src_b)?;

                let val = a.fadd(b)?;
                self.registers.insert(*dst, val);
            }
            Instruction::FSub { src_a, src_b, dst } => {
                let a = self.registers.get(src_a)?;
                let b = self.registers.get(src_b)?;

                let val = a.fsub(b)?;
                self.registers.insert(*dst, val);
            }
            Instruction::FMult { src_a, src_b, dst } => {
                let a = self.registers.get(src_a)?;
                let b = self.registers.get(src_b)?;

                let val = a.fmult(b)?;
                self.registers.insert(*dst, val);
            }
            Instruction::FDiv { src_a, src_b, dst } => {
                let a = self.registers.get(src_a)?;
                let b = self.registers.get(src_b)?;

                let val = a.fdiv(b)?;
                self.registers.insert(*dst, val);
            }
            Instruction::FComp { src_a, src_b, dst } => {
                let a = self.registers.get(src_a)?;
                let b = self.registers.get(src_b)?;

                let val = a.fsub(b)?;
                self.registers.insert(*dst, val);
            }
            Instruction::FLoad { src, dst } => {
                let stack_idx = self.registers.get(src)?;
                let val = stack[stack_idx.to_int()? as usize].clone();

                self.registers.insert(*dst, val);
            }
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
        Some(true)
    }

    pub fn curr_instruction(&self) -> Option<&Instruction> {
        let (func, stack) = self.call_stack.last()?;
        let instrs = self.functions.get(func)?;
        instrs.get(self.inst_idx).map(|(_, instr)| instr)
    }

    pub fn curr_line(&self) -> Option<usize> {
        let (func, stack) = self.call_stack.last()?;
        let instrs = self.functions.get(func)?;
        instrs.get(self.inst_idx).map(|(i, _)| *i)
    }
}

pub fn run_interpreter(iloc: IlocProgram) -> Result<(), &'static str> {
    let mut interpreter = Interpreter::new(iloc);

    let mut break_points = HashSet::new();
    let mut buf = String::new();
    let mut continue_flag = false;
    // Now we can get input from the user
    loop {
        match interpreter.run_next_instruction() {
            Some(true) => {
                let line = if let Some(l) = interpreter.curr_line() {
                    l
                } else {
                    break;
                };

                if continue_flag && !break_points.contains(&line) {
                    continue;
                }

                'dbg: loop {
                    let mut handle = std::io::stdin_locked();
                    handle.read_line(&mut buf).unwrap();
                    match buf.split_whitespace().collect::<Vec<_>>().as_slice() {
                        ["step"] | [] => {
                            break 'dbg;
                        }
                        ["cont"] => {
                            continue_flag = true;
                            break 'dbg;
                        }
                        ["printi"] => {
                            println!("{:?}", interpreter.curr_instruction());
                        }
                        ["print", reg] => {
                            if let Ok(r) = Reg::from_str(reg) {
                                if let Some(v) = interpreter.registers.get(&r) {
                                    println!("{:?}", v)
                                }
                            }
                        }
                        ["brk", lines @ ..] => {
                            break_points.extend(
                                lines
                                    .iter()
                                    .map(|s| s.parse::<usize>())
                                    .collect::<Result<Vec<_>, _>>()
                                    .unwrap(),
                            );
                        }
                        _ => {}
                    }

                    buf.clear();
                    if break_points.contains(&line) {
                        continue_flag = false;
                    }
                }
                // Always clear the debug op buffer
                buf.clear();
            }
            Some(false) => {}
            None => {
                let mut regs = interpreter
                    .registers
                    .iter()
                    .map(|(r, v)| (r, v))
                    .collect::<Vec<_>>();

                regs.sort_by(|a, b| a.0.cmp(b.0));

                println!(
                    "registers: {}",
                    regs.into_iter()
                        .map(|(r, v)| format!("({:?} {:?})", r, v))
                        .collect::<Vec<_>>()
                        .join(", ")
                );
                println!(
                    "instruction: {:?} line: {}",
                    interpreter.curr_instruction(),
                    interpreter
                        .curr_line()
                        .map(|n| n.to_string())
                        .unwrap_or_else(|| "<unknown line>".to_string())
                );
                return Err("failed at the above instruction");
            }
        }
    }

    Ok(())
}
