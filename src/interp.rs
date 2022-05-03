use std::{
	cmp::Ordering,
	collections::{BTreeMap, HashMap, HashSet},
	intrinsics::discriminant_value,
	str::FromStr,
};

use crate::iloc::{IlocProgram, Instruction, Loc, Reg, Val, NEGATIVE_UINT};

const HEAP_MASK: i32 = 1 << 31;

pub fn is_heap(addr: i32) -> bool { (addr & HEAP_MASK) == HEAP_MASK }
pub fn remove_heap_mask(addr: i32) -> i32 { addr & !HEAP_MASK }

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
	/// The heap of a program.
	///
	/// This is a cheap way of implementing malloc...
	heap: Vec<Val>,
	heap_meta: BTreeMap<i32, usize>,
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
	pub fn new(mut iloc: IlocProgram) -> Self {
		let mut preamble_lines = iloc.preamble.len();
		iloc.preamble.sort_by(|a, b| match discriminant_value(a).cmp(&discriminant_value(b)) {
			Ordering::Equal => match (a, b) {
				(Instruction::Array { name: a, .. }, Instruction::Array { name: b, .. }) => {
					a.cmp(b)
				}
				(Instruction::Global { name: a, .. }, Instruction::Global { name: b, .. }) => {
					a.cmp(b)
				}
				(Instruction::String { name: a, .. }, Instruction::String { name: b, .. }) => {
					a.cmp(b)
				}
				(Instruction::Float { name: a, .. }, Instruction::Float { name: b, .. }) => {
					a.cmp(b)
				}
				_ => unreachable!(),
			},
			val => val,
		});

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
					Some((Loc(name), Val::Integer(4 + (stack.len() - 1) as i32)))
				}
				Instruction::Global { name, size, align: _ } => {
					stack.push(Val::Null);
					Some((Loc(name), Val::Integer((stack.len() - 1) as i32)))
				}
				Instruction::String { name, mut content } => {
					content = content.replace("\\n", "\n");

					let flipped = content.chars().rev();
					let mut c = vec![];
					for el in flipped {
						c.extend(vec![Val::Null; 3]);
						c.push(Val::Integer(el as i32));
					}
					stack.extend(c);
					stack.extend(vec![Val::Null; 3]);
					// Push the size of the incoming string
					stack.push(Val::Integer(content.len() as i32));
					Some((Loc(name), Val::Integer((stack.len() - 1) as i32)))
				}
				Instruction::Float { name, content } => {
					stack.push(Val::Float(content));
					Some((Loc(name), Val::Integer((stack.len() - 1) as i32)))
				}
				_ => None,
			})
			.collect::<HashMap<_, _>>();

		// stack.extend(vec![Val::Null; STACK_SIZE]);

		// Carr's examples read of the end of an array, null is not an acceptable default
		// stack value...
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
					registers.insert(Reg::Var(0), Val::Integer((STACK_SIZE - 1) as i32));
				}

				fn_decl_map.insert(Loc(func.label.clone()), (func.stack_size, func.params));
				(Loc(func.label), instrs)
			})
			.collect();

		Self {
			data,
			heap: vec![Val::Null; STACK_SIZE],
			heap_meta: BTreeMap::new(),
			functions,
			fn_decl: fn_decl_map,
			label_map,
			inst_idx: 0,
			call_stack: vec![CallStackEntry::new("main", registers)],
			stack,
			ret_idx: vec![0],
		}
	}

	fn callee_stack_size(&self) -> i32 {
		let CallStackEntry { name, .. } = self.call_stack.last().unwrap();
		self.fn_decl.get(&Loc(name.to_string())).unwrap().0 as i32
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
			Instruction::RShiftu { src_a, src_b, dst } => {
				let a = self.registers().get(src_a)?;
				let b = self.registers().get(src_b)?;

				let val = a.rshiftu(b)?;
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
			Instruction::ImmRShiftu { src, konst, dst } => {
				let a = self.registers().get(src)?;

				let val = a.rshiftu(konst)?;
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
				let index = self.call_stack.last()?.registers.get(src)?.to_int_32()?;
				let val = if is_heap(index) {
					let index = remove_heap_mask(index);
					self.heap[index as usize].clone()
				} else {
					stack[index as usize].clone()
				};

				self.call_stack.last_mut()?.registers.insert(*dst, val);
			}
			Instruction::LoadAddImm { src, add, dst } => {
				let stack_idx = self.call_stack.last()?.registers.get(src)?.to_int_32()?;
				let index = stack_idx + add.to_int_32()?;
				let val = if is_heap(index) {
					let index = remove_heap_mask(index);
					self.heap[index as usize].clone()
				} else {
					stack[index as usize].clone()
				};
				self.call_stack.last_mut()?.registers.insert(*dst, val);
			}
			Instruction::LoadAdd { src, add, dst } => {
				let stack_idx = self.call_stack.last()?.registers.get(src)?.to_int_32()?;
				let add_amt = self.call_stack.last()?.registers.get(add)?.to_int_32()?;
				let index = stack_idx + add_amt;
				let val = if is_heap(index) {
					let index = remove_heap_mask(index);
					self.heap[index as usize].clone()
				} else {
					stack[index as usize].clone()
				};
				self.call_stack.last_mut()?.registers.insert(*dst, val);
			}
			Instruction::Store { src, dst } => {
				let val = self.call_stack.last()?.registers.get(src)?.clone();
				let index = self.call_stack.last()?.registers.get(dst)?.to_int_32()?;
				if is_heap(index) {
					let index = remove_heap_mask(index);
					self.heap[index as usize] = val;
				} else {
					stack[index as usize] = val;
				}
			}
			Instruction::StoreAddImm { src, add, dst } => {
				let val = self.call_stack.last()?.registers.get(src)?.clone();
				let stack_idx = self.call_stack.last()?.registers.get(dst)?.to_int_32()?;
				let index = stack_idx + add.to_int_32()?;
				if is_heap(index) {
					let index = remove_heap_mask(index);
					self.heap[index as usize] = val;
				} else {
					stack[index as usize] = val;
				}
			}
			Instruction::StoreAdd { src, add, dst } => {
				let val = self.call_stack.last()?.registers.get(src)?.clone();

				let add = self.call_stack.last()?.registers.get(add)?.to_int_32()?;
				let stack_idx = self.call_stack.last()?.registers.get(dst)?.to_int_32()?;
				let index = stack_idx + add;
				if is_heap(index) {
					let index = remove_heap_mask(index);
					self.heap[index as usize] = val;
				} else {
					stack[index as usize] = val;
				}
			}
			Instruction::CmpLT { a, b, dst } | Instruction::CmpuLT { a, b, dst } => {
				let a = self.registers().get(a)?;
				let b = self.registers().get(b)?;
				let val = a.cmp_lt(b)?;
				self.call_stack.last_mut()?.registers.insert(*dst, val);
			}
			Instruction::CmpLE { a, b, dst } | Instruction::CmpuLE { a, b, dst } => {
				let a = self.registers().get(a)?;
				let b = self.registers().get(b)?;
				let val = a.cmp_le(b)?;
				self.call_stack.last_mut()?.registers.insert(*dst, val);
			}
			Instruction::CmpGT { a, b, dst } | Instruction::CmpuGT { a, b, dst } => {
				let a = self.registers().get(a)?;
				let b = self.registers().get(b)?;
				let val = a.cmp_gt(b)?;
				self.call_stack.last_mut()?.registers.insert(*dst, val);
			}
			Instruction::CmpGE { a, b, dst } | Instruction::CmpuGE { a, b, dst } => {
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
			Instruction::Comp { a, b, dst } | Instruction::Compu { a, b, dst } => {
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
			Instruction::TestGT { test, dst } | Instruction::TestuGT { test, dst } => {
				let a = self.registers().get(test)?;
				let is_gt = match a {
					Val::Integer(i) if *i > 0 => 1,
					Val::UInteger(i) if *i > 0 && *i != NEGATIVE_UINT => 1,
					Val::Float(f) if *f > 0.0 => 1,
					_ => 0,
				};
				self.call_stack.last_mut()?.registers.insert(*dst, Val::Integer(is_gt));
			}
			Instruction::TestGE { test, dst } | Instruction::TestuGE { test, dst } => {
				let a = self.registers().get(test)?;
				let is_ge = match a {
					Val::Integer(i) if *i >= 0 => 1,
					Val::UInteger(i) if *i != NEGATIVE_UINT => 1,
					Val::Float(f) if *f >= 0.0 => 1,
					_ => 0,
				};
				self.call_stack.last_mut()?.registers.insert(*dst, Val::Integer(is_ge));
			}
			Instruction::TestLT { test, dst } | Instruction::TestuLT { test, dst } => {
				let a = self.registers().get(test)?;
				let is_lt = match a {
					Val::Integer(i) if *i < 0 => 1,
					Val::UInteger(i) if *i == NEGATIVE_UINT => 1,
					Val::Float(f) if *f < 0.0 => 1,
					_ => 0,
				};
				self.call_stack.last_mut()?.registers.insert(*dst, Val::Integer(is_lt));
			}
			Instruction::TestLE { test, dst } | Instruction::TestuLE { test, dst } => {
				let a = self.registers().get(test)?;
				let is_le = match a {
					Val::Integer(i) if *i <= 0 => 1,
					Val::UInteger(i) if *i == 0 || *i == NEGATIVE_UINT => 1,
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
				let val = registers.get(ret_reg)?.clone();
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
			Instruction::CbrLT { a, b, loc } | Instruction::CbruLT { a, b, loc } => {
				let a = self.registers().get(a)?;
				let b = self.registers().get(b)?;
				let should_jump = a.cmp_lt(b)?.is_one();
				if should_jump {
					let jmp_idx = self.label_map.get(loc)?;
					self.inst_idx = *jmp_idx;
					return Some(true);
				}
			}
			Instruction::CbrLE { a, b, loc } | Instruction::CbruLE { a, b, loc } => {
				let a = self.registers().get(a)?;
				let b = self.registers().get(b)?;
				let should_jump = a.cmp_le(b)?.is_one();
				if should_jump {
					let jmp_idx = self.label_map.get(loc)?;
					self.inst_idx = *jmp_idx;
					return Some(true);
				}
			}
			Instruction::CbrGT { a, b, loc } | Instruction::CbruGT { a, b, loc } => {
				let a = self.registers().get(a)?;
				let b = self.registers().get(b)?;
				let should_jump = a.cmp_gt(b)?.is_one();
				if should_jump {
					let jmp_idx = self.label_map.get(loc)?;
					self.inst_idx = *jmp_idx;
					return Some(true);
				}
			}
			Instruction::CbrGE { a, b, loc } | Instruction::CbruGE { a, b, loc } => {
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
					unsafe { f.to_int_unchecked::<i32>() }
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
				let index = stack_idx.to_int_32()?;
				let val = if is_heap(index) {
					let index = remove_heap_mask(index);
					self.heap[index as usize].clone()
				} else {
					stack[index as usize].clone()
				};

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
				let index = stack_idx.to_int_32()?;
				if is_heap(index) {
					let index = remove_heap_mask(index);
					self.heap[index as usize] = Val::Integer(buf.trim().parse().unwrap());
				} else {
					stack[index as usize] = Val::Integer(buf.trim().parse().unwrap());
				}
			}
			Instruction::FWrite(r) => {
				println!("{}", self.registers().get(r)?.to_float()?)
			}
			Instruction::IWrite(r) => {
				println!("{}", self.registers().get(r)?)
			}
			Instruction::PutChar(r) => {
				let ch = char::from_u32(self.registers().get(r)?.to_uint_32()? as u32)?;
				print!("{}", ch)
			}
			Instruction::SWrite(r) => {
				let s_idx = self.call_stack.last()?.registers.get(r)?.to_int_32()? as usize;
				let start = &stack[s_idx];

				let Val::Integer(size) = start else { return None; };
				let size = (size * 4) as usize;
				// Skip the size int we read and read some chars
				let char_idx = s_idx - 4;

				let mut text = String::new();
				for i in (0..size).step_by(4) {
					let Val::Integer(ch) = stack[char_idx - i] else { return None; };
					text.push(char::from_u32(ch as u32)?);
				}
				let text = text.trim_start_matches('"');
				let text = text.trim_end_matches('"');
				let text = text.replace("\\n", "\n");
				print!("{}", text)
			}
			Instruction::Malloc { size, dst } => {
				let addr =
					self.heap_meta.first_entry().map(|e| *e.key()).unwrap_or(STACK_SIZE as i32);
				let size = self.call_stack.last()?.registers.get(size)?.to_int_32()?;

				self.heap_meta.insert(addr, size as usize);
				self.call_stack
					.last_mut()
					.unwrap()
					.registers
					.insert(*dst, Val::Integer(addr | HEAP_MASK));
			}
			Instruction::Free(reg) => {
				let addr = self.call_stack.last()?.registers.get(reg)?.to_int_32()?;
				if !is_heap(addr) {
					return None;
				}
				let index = remove_heap_mask(addr);
				let size = self.heap_meta.remove(&index)?;

				let index = index as usize;
				for slot in &mut self.heap[index - size..index] {
					*slot = Val::Null;
				}
			}
			Instruction::Realloc { src, size, dst } => {
				let old_addr = self.call_stack.last()?.registers.get(src)?.to_int_32()?;
				// Check that this was, in fact, allocated from the heap
				if !is_heap(old_addr) {
					return None;
				}

				let old_idx = remove_heap_mask(old_addr);

				let old_size = *self.heap_meta.get(&old_idx)?;
				let size = self.call_stack.last()?.registers.get(size)?.to_int_32()? as usize;

				let old_idx = old_idx as usize;
				let mut copy_of_old_bytes = self.heap[old_idx - old_size..old_idx].to_vec();

				let addr =
					self.heap_meta.first_entry().map(|e| *e.key()).unwrap_or(STACK_SIZE as i32);
				let index = addr as usize;
				for (i, slot) in self.heap[index - size..index].iter_mut().enumerate() {
					if i >= (copy_of_old_bytes.len() - 1) {
						*slot = copy_of_old_bytes.remove(i);
					} else {
						break;
					}
				}
				self.call_stack
					.last_mut()
					.unwrap()
					.registers
					.insert(*dst, Val::Integer(addr | HEAP_MASK));
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
					if matches!(slot, Val::Null) {
						continue;
					}
					println!("{}: {:?}", idx, slot);
				}
			}
			["prints" | "ps", idx] => {
				println!("{:?}", interpreter.stack[idx.parse::<usize>().unwrap()]);
			}
			["printh" | "ph"] => {
				for (idx, slot) in interpreter.heap.iter().enumerate() {
					if matches!(slot, Val::Null) {
						continue;
					}
					println!("{}: {:?}", idx, slot);
				}
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
				println!("heap: [");
				for (idx, slot) in interpreter.heap.iter().enumerate() {
					if matches!(slot, Val::Null) {
						continue;
					}
					println!("  {}: {:?}", idx as i32 | HEAP_MASK, slot);
				}
				println!("]\nstack: [");
				for (idx, slot) in interpreter.stack.iter().enumerate() {
					if matches!(slot, Val::Null | Val::Integer(0)) {
						continue;
					}
					println!("  {}: {:?}", idx, slot);
				}
				println!("]");
				return Err("failed at the above instruction");
			}
		}
	}

	println!("number of instructions executed: {}", instruction_count);
	Ok(())
}
