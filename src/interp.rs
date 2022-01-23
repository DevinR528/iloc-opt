use std::{
    collections::{BTreeSet, HashMap, HashSet},
    io::BufRead,
    str::FromStr,
};

use crate::iloc::{parse_text, Block, Function, IlocProgram, Instruction, Loc, Reg, Val};

const STACK_SIZE: usize = 4096 * 4;

struct CallStackEntry {
    name: Loc,
    clobber_map: HashMap<Reg, Val>,
    ret_val: Option<Reg>,
}

impl CallStackEntry {
    fn new(s: &str) -> Self {
        Self { name: Loc(s.to_string()), clobber_map: HashMap::default(), ret_val: None }
    }
}

pub struct Interpreter {
    /// The data segment of a program.
    ///
    /// Name to index into the stack.
    data: HashMap<Loc, Val>,
    /// Instructions broken up into functions and blocks.
    functions: HashMap<Loc, Vec<(usize, Instruction)>>,
    /// A map of function names to stack size and parameter list.
    fn_decl: HashMap<Loc, (usize, Vec<Reg>)>,
    /// A mapping of labels names to the index of the first instruction to execute after the label.
    label_map: HashMap<Loc, usize>,
    /// A map of register to value.
    registers: HashMap<Reg, Val>,
    /// The index of which instruction we are on within a block.
    inst_idx: usize,
    /// The function call stack.
    ///
    /// A tuple of function name and any smashed registers that will need to be restored on return.
    call_stack: Vec<CallStackEntry>,
    /// The program stack, this includes the `.data` segment so we can refer to labels like
    /// pointers.
    stack: Vec<Val>,
    /// The index of the instruction to return to after a call returns.
    ret_idx: Vec<usize>,
}

impl Interpreter {
    pub fn new(iloc: IlocProgram) -> Self {
        let mut preamble_lines = iloc.preamble.len();
        let mut stack = vec![];
        let data = iloc
            .preamble
            .into_iter()
            .flat_map(|inst| match inst {
                Instruction::Global { name, size, align } => {
                    stack.push(Val::Null);
                    Some((Loc(name), Val::Integer((stack.len() - 1) as isize)))
                }
                Instruction::String { name, content } => {
                    stack.push(Val::String(content));
                    Some((Loc(name), Val::Integer((stack.len() - 1) as isize)))
                }
                Instruction::Float { name, content } => {
                    stack.push(Val::Float(content));
                    Some((Loc(name), Val::Integer((stack.len() - 1) as isize)))
                }
                _ => None,
            })
            .collect::<HashMap<_, _>>();

        stack.extend(vec![Val::Integer(0); STACK_SIZE]);

        let mut registers = HashMap::new();
        let mut label_map = HashMap::new();
        let mut fn_decl_map = HashMap::new();
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

                if func.label == "main" {
                    // This is the data stack pointer, in a real program it would be a pointer to
                    // the memory address of the beginning of the program
                    // itself, since our stack is separate it's just the end
                    // index of the stack since it grows towards index 0 from index (length)
                    registers.insert(Reg::Var(0), Val::Integer(STACK_SIZE as isize));
                }

                fn_decl_map.insert(Loc(func.label.clone()), (func.stack_size, func.params));
                (Loc(func.label), instrs)
            })
            .collect();

        Self {
            data,
            functions,
            fn_decl: fn_decl_map,
            label_map,
            registers,
            inst_idx: 0,
            call_stack: vec![CallStackEntry::new("main")],
            stack,
            ret_idx: vec![0],
        }
    }

    fn callee_stack_size(&self) -> isize {
        let CallStackEntry { name, .. } = self.call_stack.last().unwrap();
        self.fn_decl.get(&Loc(name.to_string())).unwrap().0 as isize
    }

    pub fn run_next_instruction(&mut self, count: &mut usize) -> Option<bool> {
        if self.call_stack.is_empty() {
            return Some(false);
        }

        // println!(
        //     "// line    {}  {}",
        //     self.curr_line().unwrap(),
        //     self.curr_instruction().unwrap()
        // );

        let CallStackEntry { name: func, .. } = self.call_stack.last_mut().unwrap();
        let stack = &mut self.stack;
        let instrs = self.functions.get(func).unwrap();

        // Skip these instructions
        match instrs[self.inst_idx].1 {
            Instruction::Frame { .. } | Instruction::Label(..) => {
                *count += 1;
                self.inst_idx += 1
            }
            _ => {}
        }

        match &instrs[self.inst_idx].1 {
            Instruction::I2I { src, dst } => {
                self.registers.insert(*dst, self.registers.get(src).cloned()?);
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
                stack[stack_idx] = val;
            }
            Instruction::StoreAddImm { src, add, dst } => {
                let val = self.registers.get(src)?.clone();
                let stack_idx = self.registers.get(dst)?.to_int()? as usize;
                stack[stack_idx + (add.to_int()? as usize)] = val;
            }
            Instruction::StoreAdd { src, add, dst } => {
                let val = self.registers.get(src)?.clone();

                let add = self.registers.get(add)?.to_int()? as usize;
                let stack_idx = self.registers.get(dst)?.to_int()? as usize;

                stack[stack_idx + add] = val;
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
                self.registers.insert(*dst, Val::Integer(if is_eq { 1 } else { 0 }));
            }
            Instruction::TestNE { test, dst } => {
                let a = self.registers.get(test)?;
                let is_ne = !a.is_zero();
                self.registers.insert(*dst, Val::Integer(if is_ne { 1 } else { 0 }));
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
                self.inst_idx = 0;
                let (size, params) = self.fn_decl.get(&Loc(name.to_owned())).unwrap();

                self.call_stack.push(CallStackEntry {
                    name: Loc(name.to_owned()),
                    // Save all the call clobbered registers
                    clobber_map: params
                        .iter()
                        // Save the stack pointer
                        .chain(std::iter::once(&Reg::Var(0)))
                        .filter_map(|r| Some((*r, self.registers.get(r)?.clone())))
                        .collect(),
                    ret_val: None,
                });

                assert_eq!(params.len(), args.len());
                for (param, arg) in params.iter().zip(args) {
                    self.registers.insert(*param, self.registers.get(arg).unwrap().clone());
                }

                // New stack pointer (vr0)
                let new_ip = self
                    .registers
                    .get(&Reg::Var(0))
                    .unwrap()
                    .sub(&Val::Integer(*size as isize))
                    .unwrap();
                self.registers.insert(Reg::Var(0), new_ip);

                return Some(true);
            }
            Instruction::ImmCall { name, args, ret } => {
                self.ret_idx.push(self.inst_idx + 1);
                self.inst_idx = 0;
                let shift_stack = self.callee_stack_size();
                let (size, params) = self.fn_decl.get(&Loc(name.to_owned())).unwrap();

                self.call_stack.push(CallStackEntry {
                    name: Loc(name.to_owned()),
                    // Save all the call clobbered registers
                    clobber_map: params
                        .iter()
                        // Save the stack pointer
                        .chain(std::iter::once(&Reg::Var(0)))
                        .filter_map(|r| Some((*r, self.registers.get(r)?.clone())))
                        .collect(),
                    ret_val: Some(*ret),
                });

                assert_eq!(params.len(), args.len());
                for (param, arg) in params.iter().zip(args) {
                    self.registers.insert(*param, self.registers.get(arg).unwrap().clone());
                }

                // New stack pointer (vr0)
                let new_ip = self
                    .registers
                    .get(&Reg::Var(0))
                    .unwrap()
                    .sub(&Val::Integer(shift_stack))
                    .unwrap();
                self.registers.insert(Reg::Var(0), new_ip);

                return Some(true);
            }
            Instruction::ImmRCall { reg, args, ret } => todo!(),
            Instruction::Ret => {
                self.inst_idx = self.ret_idx.pop()?;
                let CallStackEntry { name, clobber_map, ret_val } = self.call_stack.pop()?;

                // Restore the call clobbered registers
                for (reg, val) in clobber_map {
                    self.registers.insert(reg, val);
                }

                assert!(ret_val.is_none());

                return Some(true);
            }
            Instruction::ImmRet(ret_reg) => {
                self.inst_idx = self.ret_idx.pop()?;
                let CallStackEntry { name, clobber_map, ret_val } = self.call_stack.pop()?;

                // Restore the call clobbered registers
                for (reg, val) in clobber_map {
                    self.registers.insert(reg, val);
                }

                let dst = ret_val.unwrap();
                let val = self.registers.get(ret_reg).unwrap().clone();
                self.registers.insert(dst, val);

                return Some(true);
            }
            // cbr
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
            // cbrne
            Instruction::CbrF { cond, loc } => {
                let a = self.registers.get(cond)?;
                let should_jump = match a {
                    Val::Integer(i) if *i == 0 => true,
                    Val::Float(f) if *f == 0.0 => true,
                    _ => false,
                };
                // This is conditional branch if NOT equal
                if should_jump {
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
                todo!();

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
                todo!();
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
                self.registers.insert(*dst, self.registers.get(src).cloned()?);
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

                self.registers.insert(*r, Val::Float(buf.trim().parse::<f64>().unwrap()));
            }
            Instruction::IRead(r) => {
                let mut buf = String::new();
                let mut handle = std::io::stdin_locked();
                handle.read_line(&mut buf).unwrap();

                let stack_idx = self.registers.get(r)?;
                stack[stack_idx.to_int().unwrap() as usize] =
                    Val::Integer(buf.trim().parse().unwrap());
            }
            Instruction::FWrite(r) => println!("{:?}", self.registers.get(r)?.to_float()?),
            Instruction::IWrite(r) => println!("{:?}", self.registers.get(r)?.to_int()?),
            Instruction::SWrite(r) => {
                println!("{:?}", stack[self.registers.get(r)?.to_int()? as usize])
            }
            _ => todo!("{:?}", instrs[self.inst_idx]),
        }
        self.inst_idx += 1;
        Some(true)
    }

    pub fn curr_instruction(&self) -> Option<&Instruction> {
        let func = &self.call_stack.last()?.name;
        let instrs = self.functions.get(func)?;
        instrs.get(self.inst_idx).map(|(_, instr)| instr)
    }

    pub fn curr_line(&self) -> Option<usize> {
        let func = &self.call_stack.last()?.name;
        let instrs = self.functions.get(func)?;
        instrs.get(self.inst_idx).map(|(i, _)| *i)
    }
}

fn debug_loop(
    buf: &mut String,
    break_points: &mut HashSet<usize>,
    interpreter: &mut Interpreter,
    continue_flag: &mut bool,
    line: usize,
) {
    if *continue_flag && !break_points.contains(&line) {
        return;
    }

    'dbg: loop {
        let mut handle = std::io::stdin_locked();
        handle.read_line(buf).unwrap();
        match buf.split_whitespace().collect::<Vec<_>>().as_slice() {
            ["step" | "s"] | [] => {
                break 'dbg;
            }
            ["cont" | "c"] => {
                *continue_flag = true;
                break 'dbg;
            }
            ["printi" | "pi"] => {
                println!("{:?}", interpreter.curr_instruction());
            }
            ["printc" | "pc"] => {
                println!(
                    "{:?}",
                    interpreter
                        .call_stack
                        .iter()
                        .map(|cse| cse.name.0.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                );
            }
            ["prints" | "ps", idx] => {
                println!("{:?}", interpreter.stack[idx.parse::<usize>().unwrap()]);
            }
            ["print" | "p", reg] => {
                let reg =
                    if !reg.starts_with("%vr") { format!("%vr{}", reg) } else { reg.to_string() };
                if let Ok(r) = Reg::from_str(&reg) {
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
            *continue_flag = false;
        }
    }
    // Always clear the debug op buffer
    buf.clear();
}

pub fn run_interpreter(iloc: IlocProgram) -> Result<(), &'static str> {
    let mut instruction_count = 0;
    let mut interpreter = Interpreter::new(iloc);

    let mut break_points = HashSet::new();
    let mut buf = String::new();
    let mut continue_flag = false;
    // Now we can get input from the user
    loop {
        match interpreter.run_next_instruction(&mut instruction_count) {
            Some(true) => {
                let line = if let Some(l) = interpreter.curr_line() {
                    l
                } else {
                    break;
                };

                instruction_count += 1;

                debug_loop(&mut buf, &mut break_points, &mut interpreter, &mut continue_flag, line);
            }
            Some(false) => {}
            None => {
                let mut regs =
                    interpreter.registers.iter().map(|(r, v)| (r, v)).collect::<Vec<_>>();

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

    println!("number of instructions executed: {}", instruction_count);
    Ok(())
}
