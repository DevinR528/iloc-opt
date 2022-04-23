use std::{
    collections::{HashMap, HashSet},
    str::FromStr,
};

use crate::iloc::{IlocProgram, Instruction, Loc, Reg, Val};

const STACK_SIZE: usize = 4096 * 4 * 4;

struct CallStackEntry {
    name: Loc,
    registers: HashMap<Reg, Val>,
    ret_val: Option<Reg>,
}

impl CallStackEntry {
    fn new(s: &str, registers: HashMap<Reg, Val>) -> Self {
        Self { name: Loc(s.to_string()), registers, ret_val: None }
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
    /// A mapping of labels names to the index of the first instruction to execute after
    /// the label.
    label_map: HashMap<Loc, usize>,
    /// The index of which instruction we are on within a block.
    inst_idx: usize,
    /// The function call stack.
    ///
    /// A tuple of function name and any smashed registers that will need to be restored
    /// on return.
    call_stack: Vec<CallStackEntry>,
    /// The program stack, this includes the `.data` segment so we can refer to labels
    /// like pointers.
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
                Instruction::Array { name, size, mut content } => {
                    content.reverse();
                    let mut c = vec![];
                    for el in content {
                        c.extend(vec![Val::Null; 3]);
                        c.push(el);

                    }
                    stack.extend(c);
                    Some((Loc(name), Val::Integer(4 + (stack.len() - 1) as isize)))
                }
                Instruction::Global { name, size, align: _ } => {
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
                        label_map.insert(Loc(s.to_string()), idx);
                    }
                    instrs.push((preamble_lines, inst.clone()));
                }

                if func.label == "main" {
                    // This is the data stack pointer, in a real program it would be a
                    // pointer to the memory address of the beginning
                    // of the program itself, since our stack is
                    // separate it's just the end index of the stack
                    // since it grows towards index 0 from index (length)
                    registers.insert(Reg::Var(0), Val::Integer((STACK_SIZE - 1) as isize));
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
            inst_idx: 0,
            call_stack: vec![CallStackEntry::new("main", registers)],
            stack,
            ret_idx: vec![0],
        }
    }

    fn callee_stack_size(&self) -> isize {
        let CallStackEntry { name, .. } = self.call_stack.last().unwrap();
        self.fn_decl.get(&Loc(name.to_string())).unwrap().0 as isize
    }

    fn registers(&self) -> &HashMap<Reg, Val> { &self.call_stack.last().unwrap().registers }

    pub fn run_next_instruction(&mut self) -> Option<bool> {
        if self.call_stack.is_empty() {
            return Some(false);
        }

        let CallStackEntry { name: func, .. } = self.call_stack.last()?;
        let stack = &mut self.stack;
        let instrs = self.functions.get(func)?;

        // Skip these instructions
        while let Instruction::Skip(..) | Instruction::Label(..) | Instruction::Frame { .. } =
            instrs[self.inst_idx].1
        {
            self.inst_idx += 1;
            if self.inst_idx == (instrs.len() - 1) {
                return Some(false);
            }
        }

        match &instrs[self.inst_idx].1 {
            Instruction::I2I { src, dst } => {
                let val = self.registers().get(src).cloned()?;
                self.call_stack.last_mut()?.registers.insert(*dst, val);
            }
            Instruction::Add { src_a, src_b, dst } => {
                let a = self.registers().get(src_a)?;
                let b = self.registers().get(src_b)?;

                let val = a.add(b)?;
                self.call_stack.last_mut()?.registers.insert(*dst, val);
            }
            Instruction::Sub { src_a, src_b, dst } => {
                let a = self.registers().get(src_a)?;
                let b = self.registers().get(src_b)?;

                let val = a.sub(b)?;
                self.call_stack.last_mut()?.registers.insert(*dst, val);
            }
            Instruction::Mult { src_a, src_b, dst } => {
                let a = self.registers().get(src_a)?;
                let b = self.registers().get(src_b)?;

                let val = a.mult(b)?;
                self.call_stack.last_mut()?.registers.insert(*dst, val);
            }
            Instruction::LShift { src_a, src_b, dst } => {
                let a = self.registers().get(src_a)?;
                let b = self.registers().get(src_b)?;

                let val = a.lshift(b)?;
                self.call_stack.last_mut()?.registers.insert(*dst, val);
            }
            Instruction::RShift { src_a, src_b, dst } => {
                let a = self.registers().get(src_a)?;
                let b = self.registers().get(src_b)?;

                let val = a.rshift(b)?;
                self.call_stack.last_mut()?.registers.insert(*dst, val);
            }
            Instruction::Mod { src_a, src_b, dst } => {
                let a = self.registers().get(src_a)?;
                let b = self.registers().get(src_b)?;

                let val = a.modulus(b)?;
                self.call_stack.last_mut()?.registers.insert(*dst, val);
            }
            Instruction::Div { src_a, src_b, dst } => {
                let a = self.registers().get(src_a)?;
                let b = self.registers().get(src_b)?;

                let val = a.divide(b)?;
                self.call_stack.last_mut()?.registers.insert(*dst, val);
            }
            Instruction::And { src_a, src_b, dst } => {
                let a = self.registers().get(src_a)?;
                let b = self.registers().get(src_b)?;

                let val = a.and(b)?;
                self.call_stack.last_mut()?.registers.insert(*dst, val);
            }
            Instruction::Or { src_a, src_b, dst } => {
                let a = self.registers().get(src_a)?;
                let b = self.registers().get(src_b)?;

                let val = a.or(b)?;
                self.call_stack.last_mut()?.registers.insert(*dst, val);
            }
            Instruction::Not { src, dst } => {
                let a = self.registers().get(src)?;

                if let Val::Integer(int) = a.clone() {
                    self.call_stack.last_mut()?.registers.insert(*dst, Val::Integer(!int));
                }
            }
            Instruction::ImmAdd { src, konst, dst } => {
                let a = self.registers().get(src)?;

                let val = a.add(konst)?;
                self.call_stack.last_mut()?.registers.insert(*dst, val);
            }
            Instruction::ImmSub { src, konst, dst } => {
                let a = self.registers().get(src)?;

                let val = a.sub(konst)?;
                self.call_stack.last_mut()?.registers.insert(*dst, val);
            }
            Instruction::ImmMult { src, konst, dst } => {
                let a = self.registers().get(src)?;

                let val = a.mult(konst)?;
                self.call_stack.last_mut()?.registers.insert(*dst, val);
            }
            Instruction::ImmLShift { src, konst, dst } => {
                let a = self.registers().get(src)?;

                let val = a.lshift(konst)?;
                self.call_stack.last_mut()?.registers.insert(*dst, val);
            }
            Instruction::ImmRShift { src, konst, dst } => {
                let a = self.registers().get(src)?;

                let val = a.rshift(konst)?;
                self.call_stack.last_mut()?.registers.insert(*dst, val);
            }
            Instruction::ImmLoad { src, dst } => {
                let src = if let Val::Location(s) = src {
                    self.data.get(&Loc(s.to_owned()))?.clone()
                } else {
                    src.clone()
                };
                self.call_stack.last_mut()?.registers.insert(*dst, src);
            }
            Instruction::Load { src, dst } => {
                let stack_idx = self.call_stack.last()?.registers.get(src)?.to_int()?;
                let val = stack[stack_idx as usize].clone();

                self.call_stack.last_mut()?.registers.insert(*dst, val);
            }
            Instruction::LoadAddImm { src, add, dst } => {
                let stack_idx = self.call_stack.last()?.registers.get(src)?.to_int()?;
                let val = stack[(stack_idx + add.to_int()?) as usize].clone();
                self.call_stack.last_mut()?.registers.insert(*dst, val);
            }
            Instruction::LoadAdd { src, add, dst } => {
                let stack_idx = self.call_stack.last()?.registers.get(src)?.to_int()?;
                let add_amt = self.call_stack.last()?.registers.get(add)?.to_int()?;

                let val = stack[(stack_idx + add_amt) as usize].clone();
                self.call_stack.last_mut()?.registers.insert(*dst, val);
            }
            Instruction::Store { src, dst } => {
                let val = self.call_stack.last()?.registers.get(src)?.clone();
                let stack_idx = self.call_stack.last()?.registers.get(dst)?.to_int()?;

                stack[stack_idx as usize] = val;
            }
            Instruction::StoreAddImm { src, add, dst } => {
                let val = self.call_stack.last()?.registers.get(src)?.clone();
                let stack_idx = self.call_stack.last()?.registers.get(dst)?.to_int()?;

                stack[(stack_idx + add.to_int()?) as usize] = val;
            }
            Instruction::StoreAdd { src, add, dst } => {
                let val = self.call_stack.last()?.registers.get(src)?.clone();

                let add = self.call_stack.last()?.registers.get(add)?.to_int()?;
                let stack_idx = self.call_stack.last()?.registers.get(dst)?.to_int()?;

                stack[(stack_idx + add) as usize] = val;
            }
            Instruction::CmpLT { a, b, dst } => {
                let a = self.registers().get(a)?;
                let b = self.registers().get(b)?;
                let val = a.cmp_lt(b)?;
                self.call_stack.last_mut()?.registers.insert(*dst, val);
            }
            Instruction::CmpLE { a, b, dst } => {
                let a = self.registers().get(a)?;
                let b = self.registers().get(b)?;
                let val = a.cmp_le(b)?;
                self.call_stack.last_mut()?.registers.insert(*dst, val);
            }
            Instruction::CmpGT { a, b, dst } => {
                let a = self.registers().get(a)?;
                let b = self.registers().get(b)?;
                let val = a.cmp_gt(b)?;
                self.call_stack.last_mut()?.registers.insert(*dst, val);
            }
            Instruction::CmpGE { a, b, dst } => {
                let a = self.registers().get(a)?;
                let b = self.registers().get(b)?;
                let val = a.cmp_ge(b)?;
                self.call_stack.last_mut()?.registers.insert(*dst, val);
            }
            Instruction::CmpEQ { a, b, dst } => {
                let a = self.registers().get(a)?;
                let b = self.registers().get(b)?;
                let val = a.cmp_eq(b)?;
                self.call_stack.last_mut()?.registers.insert(*dst, val);
            }
            Instruction::CmpNE { a, b, dst } => {
                let a = self.registers().get(a)?;
                let b = self.registers().get(b)?;
                let val = a.cmp_ne(b)?;
                self.call_stack.last_mut()?.registers.insert(*dst, val);
            }
            Instruction::Comp { a, b, dst } => {
                let a = self.registers().get(a)?;
                let b = self.registers().get(b)?;

                let val = a.comp(b)?;
                self.call_stack.last_mut()?.registers.insert(*dst, val);
            }
            Instruction::TestEQ { test, dst } => {
                let a = self.registers().get(test)?;
                let is_eq = a.is_zero();
                self.call_stack
                    .last_mut()
                    .unwrap()
                    .registers
                    .insert(*dst, Val::Integer(if is_eq { 1 } else { 0 }));
            }
            Instruction::TestNE { test, dst } => {
                let a = self.registers().get(test)?;
                let is_ne = !a.is_zero();
                self.call_stack
                    .last_mut()
                    .unwrap()
                    .registers
                    .insert(*dst, Val::Integer(if is_ne { 1 } else { 0 }));
            }
            Instruction::TestGT { test, dst } => {
                let a = self.registers().get(test)?;
                let is_gt = match a {
                    Val::Integer(i) if *i > 0 => 1,
                    Val::Float(f) if *f > 0.0 => 1,
                    _ => 0,
                };
                self.call_stack.last_mut()?.registers.insert(*dst, Val::Integer(is_gt));
            }
            Instruction::TestGE { test, dst } => {
                let a = self.registers().get(test)?;
                let is_ge = match a {
                    Val::Integer(i) if *i >= 0 => 1,
                    Val::Float(f) if *f >= 0.0 => 1,
                    _ => 0,
                };
                self.call_stack.last_mut()?.registers.insert(*dst, Val::Integer(is_ge));
            }
            Instruction::TestLT { test, dst } => {
                let a = self.registers().get(test)?;
                let is_lt = match a {
                    Val::Integer(i) if *i < 0 => 1,
                    Val::Float(f) if *f < 0.0 => 1,
                    _ => 0,
                };
                self.call_stack.last_mut()?.registers.insert(*dst, Val::Integer(is_lt));
            }
            Instruction::TestLE { test, dst } => {
                let a = self.registers().get(test)?;
                let is_le = match a {
                    Val::Integer(i) if *i <= 0 => 1,
                    Val::Float(f) if *f <= 0.0 => 1,
                    _ => 0,
                };
                self.call_stack.last_mut()?.registers.insert(*dst, Val::Integer(is_le));
            }
            Instruction::ImmJump(loc) => {
                let jmp_idx = self.label_map.get(loc)?;
                self.inst_idx = *jmp_idx;
                return Some(true);
            }
            Instruction::Jump(_reg) => todo!(),
            Instruction::Call { name, args } => {
                self.ret_idx.push(self.inst_idx + 1);
                self.inst_idx = 0;
                let shift_stack = self.callee_stack_size();
                let (_, params) = self.fn_decl.get(&Loc(name.to_owned())).unwrap();

                let mut registers = HashMap::new();
                // New stack pointer (vr0)
                let new_ip = self
                    .registers()
                    .get(&Reg::Var(0))
                    .unwrap()
                    .sub(&Val::Integer(shift_stack))
                    .unwrap();
                registers.insert(Reg::Var(0), new_ip);

                assert_eq!(params.len(), args.len());
                for (param, arg) in params.iter().zip(args) {
                    registers.insert(*param, self.registers().get(arg)?.clone());
                }

                self.call_stack.push(CallStackEntry {
                    name: Loc(name.to_owned()),
                    registers,
                    ret_val: None,
                });

                return Some(true);
            }
            Instruction::ImmCall { name, args, ret } => {
                self.ret_idx.push(self.inst_idx + 1);
                self.inst_idx = 0;
                let shift_stack = self.callee_stack_size();
                let (_, params) = self.fn_decl.get(&Loc(name.to_owned())).unwrap();

                let mut registers = HashMap::new();
                // New stack pointer (vr0)
                let new_ip = self
                    .registers()
                    .get(&Reg::Var(0))
                    .unwrap()
                    .sub(&Val::Integer(shift_stack))
                    .unwrap();
                registers.insert(Reg::Var(0), new_ip);

                assert_eq!(params.len(), args.len());
                for (param, arg) in params.iter().zip(args) {
                    registers.insert(*param, self.registers().get(arg).unwrap().clone());
                }

                self.call_stack.push(CallStackEntry {
                    name: Loc(name.to_owned()),
                    registers,
                    ret_val: Some(*ret),
                });

                return Some(true);
            }
            Instruction::ImmRCall { reg: _, args: _, ret: _ } => todo!(),
            Instruction::Ret => {
                self.inst_idx = self.ret_idx.pop()?;
                let CallStackEntry { ret_val, .. } = self.call_stack.pop()?;

                assert!(ret_val.is_none());

                return Some(true);
            }
            Instruction::ImmRet(ret_reg) => {
                self.inst_idx = self.ret_idx.pop()?;
                let CallStackEntry { ret_val, registers, .. } = self.call_stack.pop()?;

                let dst = ret_val.unwrap();
                let val = registers.get(ret_reg).unwrap().clone();
                self.call_stack.last_mut()?.registers.insert(dst, val);

                return Some(true);
            }
            // cbr
            Instruction::CbrT { cond, loc } => {
                let a = self.registers().get(cond)?;
                let should_jump = a.is_one();
                if should_jump {
                    let jmp_idx = self.label_map.get(loc).unwrap();
                    self.inst_idx = *jmp_idx;
                    return Some(true);
                }
            }
            // cbrne
            Instruction::CbrF { cond, loc } => {
                let a = self.registers().get(cond)?;
                let should_jump = a.is_zero();
                // This is conditional branch if NOT equal
                if should_jump {
                    let jmp_idx = self.label_map.get(loc)?;
                    self.inst_idx = *jmp_idx;
                    return Some(true);
                }
            }
            Instruction::CbrLT { a, b, loc } => {
                let a = self.registers().get(a)?;
                let b = self.registers().get(b)?;
                let should_jump = a.cmp_lt(b)?.is_one();
                if should_jump {
                    let jmp_idx = self.label_map.get(loc)?;
                    self.inst_idx = *jmp_idx;
                    return Some(true);
                }
            }
            Instruction::CbrLE { a, b, loc } => {
                let a = self.registers().get(a)?;
                let b = self.registers().get(b)?;
                let should_jump = a.cmp_le(b)?.is_one();
                if should_jump {
                    let jmp_idx = self.label_map.get(loc)?;
                    self.inst_idx = *jmp_idx;
                    return Some(true);
                }
            }
            Instruction::CbrGT { a, b, loc } => {
                let a = self.registers().get(a)?;
                let b = self.registers().get(b)?;
                let should_jump = a.cmp_gt(b)?.is_one();
                if should_jump {
                    let jmp_idx = self.label_map.get(loc)?;
                    self.inst_idx = *jmp_idx;
                    return Some(true);
                }
            }
            Instruction::CbrGE { a, b, loc } => {
                let a = self.registers().get(a)?;
                let b = self.registers().get(b)?;
                let should_jump = a.cmp_ge(b)?.is_one();
                if should_jump {
                    let jmp_idx = self.label_map.get(loc)?;
                    self.inst_idx = *jmp_idx;
                    return Some(true);
                }
            }
            Instruction::CbrEQ { a, b, loc } => {
                let a = self.registers().get(a)?;
                let b = self.registers().get(b)?;
                let should_jump = a.cmp_eq(b)?.is_one();
                if should_jump {
                    let jmp_idx = self.label_map.get(loc)?;
                    self.inst_idx = *jmp_idx;
                    return Some(true);
                }
            }
            Instruction::CbrNE { a, b, loc } => {
                let a = self.registers().get(a)?;
                let b = self.registers().get(b)?;
                let should_jump = a.cmp_ne(b)?.is_one();
                if should_jump {
                    let jmp_idx = self.label_map.get(loc)?;
                    self.inst_idx = *jmp_idx;
                    return Some(true);
                }
            }
            Instruction::F2I { src, dst } => {
                let int_from_float = if let Val::Float(f) = self.registers().get(src).cloned()? {
                    unsafe { f.to_int_unchecked::<isize>() }
                } else {
                    todo!("float error {:?}", self.registers().get(src).cloned())
                };
                self.call_stack
                    .last_mut()
                    .unwrap()
                    .registers
                    .insert(*dst, Val::Integer(int_from_float));
            }
            Instruction::I2F { src, dst } => {
                let float_from_int =
                    if let Val::Integer(i) = self.registers().get(src).cloned().unwrap() {
                        i as f64
                    } else {
                        todo!("integer error")
                    };
                self.call_stack
                    .last_mut()
                    .unwrap()
                    .registers
                    .insert(*dst, Val::Float(float_from_int));
            }
            Instruction::F2F { src, dst } => {
                let val = self.registers().get(src).cloned()?;
                self.call_stack.last_mut()?.registers.insert(*dst, val);
            }
            Instruction::FAdd { src_a, src_b, dst } => {
                let a = self.registers().get(src_a)?;
                let b = self.registers().get(src_b)?;

                let val = a.fadd(b)?;
                self.call_stack.last_mut()?.registers.insert(*dst, val);
            }
            Instruction::FSub { src_a, src_b, dst } => {
                let a = self.registers().get(src_a)?;
                let b = self.registers().get(src_b)?;

                let val = a.fsub(b)?;
                self.call_stack.last_mut()?.registers.insert(*dst, val);
            }
            Instruction::FMult { src_a, src_b, dst } => {
                let a = self.registers().get(src_a)?;
                let b = self.registers().get(src_b)?;

                let val = a.fmult(b)?;
                self.call_stack.last_mut()?.registers.insert(*dst, val);
            }
            Instruction::FDiv { src_a, src_b, dst } => {
                let a = self.registers().get(src_a)?;
                let b = self.registers().get(src_b)?;

                let val = a.fdiv(b)?;
                self.call_stack.last_mut()?.registers.insert(*dst, val);
            }
            Instruction::FComp { src_a, src_b, dst } => {
                let a = self.registers().get(src_a)?;
                let b = self.registers().get(src_b)?;

                let val = a.fsub(b)?;
                self.call_stack.last_mut()?.registers.insert(*dst, val);
            }
            Instruction::FLoad { src, dst } => {
                let stack_idx = self.call_stack.last()?.registers.get(src)?;
                let val = stack[stack_idx.to_int()? as usize].clone();

                self.call_stack.last_mut()?.registers.insert(*dst, val);
            }
            Instruction::FLoadAddImm { src: _, add: _, dst: _ } => todo!(),
            Instruction::FLoadAdd { src: _, add: _, dst: _ } => todo!(),
            Instruction::FRead(r) => {
                let mut buf = String::new();
                let handle = std::io::stdin();
                handle.read_line(&mut buf).unwrap();

                self.call_stack
                    .last_mut()
                    .unwrap()
                    .registers
                    .insert(*r, Val::Float(buf.trim().parse::<f64>().unwrap()));
            }
            Instruction::IRead(r) => {
                let mut buf = String::new();
                let handle = std::io::stdin();
                handle.read_line(&mut buf).unwrap();

                let stack_idx = self.call_stack.last()?.registers.get(r)?;
                stack[stack_idx.to_int().unwrap() as usize] =
                    Val::Integer(buf.trim().parse().unwrap());
            }
            Instruction::FWrite(r) => {
                println!("{}", self.registers().get(r)?.to_float()?)
            }
            Instruction::IWrite(r) => {
                println!("{}", self.registers().get(r)?.to_int()?)
            }
            Instruction::PutChar(r) => {
                print!("{}", char::from_u32(self.registers().get(r)?.to_int()? as u32).unwrap())
            }
            Instruction::SWrite(r) => {
                let text = &stack[self.call_stack.last()?.registers.get(r)?.to_int()? as usize];
                let Val::String(text) = text else { return None; };
                let text = text.trim_start_matches('"');
                let text = text.trim_end_matches('"');
                let text = text.replace("\\n", "\n");
                print!("{}", text)
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
        let handle = std::io::stdin();
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
            ["prints" | "ps"] => {
                for (idx, slot) in interpreter.stack.iter().enumerate() {
                    if matches!(slot, Val::Null | Val::Integer(0)) { continue; }
                    println!("{}: {:?}", idx, slot);
                }
            }
            ["prints" | "ps", idx] => {
                println!("{:?}", interpreter.stack[idx.parse::<usize>().unwrap()]);
            }
            ["print" | "p", reg] => {
                let reg =
                    if !reg.starts_with("%vr") { format!("%vr{}", reg) } else { reg.to_string() };
                if let Ok(r) = Reg::from_str(&reg) {
                    if let Some(v) = interpreter.call_stack.last().unwrap().registers.get(&r) {
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

pub fn run_interpreter(iloc: IlocProgram, debug: bool) -> Result<(), &'static str> {
    let mut instruction_count = 0;
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

                instruction_count += 1;

                if debug {
                    debug_loop(
                        &mut buf,
                        &mut break_points,
                        &mut interpreter,
                        &mut continue_flag,
                        line,
                    )
                };
            }
            Some(false) => {}
            None => {
                let mut regs = interpreter
                    .call_stack
                    .last()
                    .unwrap()
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

    println!("number of instructions executed: {}", instruction_count);
    Ok(())
}
