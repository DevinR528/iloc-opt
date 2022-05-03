use std::{
	cmp::Ordering,
	collections::BTreeSet,
	fmt,
	hash::{self, Hash},
	mem::discriminant,
	str::FromStr,
	usize,
};

pub const NEGATIVE_UINT: u32 = 0xffffffff;

#[derive(Clone, Debug)]
pub enum Val {
	Integer(i32),
	UInteger(u32),
	Float(f64),
	Location(String),
	String(String),
	Null,
}

impl Val {
	pub fn to_int_32(&self) -> Option<i32> {
		if let Self::Integer(int) = self {
			return Some(*int as i32);
		}
		None
	}

	pub fn to_float(&self) -> Option<f64> {
		if let Self::Float(fl) = self {
			return Some(*fl);
		}
		None
	}

	pub fn to_uint_32(&self) -> Option<u32> {
		if let Self::UInteger(uint) = self {
			return Some(*uint);
		} else if let Self::Integer(int) = self {
			return Some(*int as u32);
		}
		None
	}

	pub fn add(&self, other: &Self) -> Option<Self> {
		if let (Self::UInteger(a), b) | (b, Self::UInteger(a)) = (self, other) {
			return Some(Self::UInteger(a.wrapping_add(b.to_uint_32()?)));
		}
		Some(Self::Integer(self.to_int_32()?.wrapping_add(other.to_int_32()?)))
	}

	pub fn sub(&self, other: &Self) -> Option<Self> {
		if let (Self::UInteger(a), b) = (self, other) {
			return Some(Self::UInteger(a.wrapping_sub(b.to_uint_32()?)));
		} else if let (a, Self::UInteger(b)) = (self, other) {
			return Some(Self::UInteger(a.to_uint_32()?.wrapping_sub(*b)));
		}
		Some(Self::Integer(self.to_int_32()?.wrapping_sub(other.to_int_32()?)))
	}

	pub fn mult(&self, other: &Self) -> Option<Self> {
		if let (Self::UInteger(a), b) = (self, other) {
			return Some(Self::UInteger(a.wrapping_mul(b.to_uint_32()?)));
		} else if let (a, Self::UInteger(b)) = (self, other) {
			return Some(Self::UInteger(a.to_uint_32()?.wrapping_mul(*b)));
		}

		Some(Self::Integer(self.to_int_32()?.wrapping_mul(other.to_int_32()?)))
	}

	/// Left shift `<<`
	pub fn lshift(&self, other: &Self) -> Option<Self> {
		if let (Self::UInteger(a), b) = (self, other) {
			return Some(Self::UInteger(a.wrapping_shl(b.to_uint_32()?)));
		} else if let (a, Self::UInteger(b)) = (self, other) {
			return Some(Self::UInteger(a.to_uint_32()?.wrapping_shl(*b)));
		}
		Some(Self::Integer(self.to_int_32()?.wrapping_shl(other.to_int_32()? as u32)))
	}

	/// Right shift `>>`
	pub fn rshift(&self, other: &Self) -> Option<Self> {
		Some(Self::Integer(self.to_int_32()?.wrapping_shr(other.to_int_32()? as u32)))
	}

	pub fn rshiftu(&self, other: &Self) -> Option<Self> {
		Some(Self::UInteger(self.to_uint_32()?.wrapping_shr(other.to_uint_32()?)))
	}

	pub fn modulus(&self, other: &Self) -> Option<Self> {
		if let (Self::UInteger(a), b) = (self, other) {
			return Some(Self::UInteger(a % b.to_uint_32()?));
		} else if let (a, Self::UInteger(b)) = (self, other) {
			return Some(Self::UInteger(a.to_uint_32()? % b));
		}
		Some(Self::Integer(self.to_int_32()? % other.to_int_32()?))
	}

	pub fn divide(&self, other: &Self) -> Option<Self> {
		if let (Self::UInteger(a), b) = (self, other) {
			return Some(Self::UInteger(a / b.to_uint_32()?));
		} else if let (a, Self::UInteger(b)) = (self, other) {
			return Some(Self::UInteger(a.to_uint_32()? / b));
		}
		Some(Self::Integer(self.to_int_32()? / other.to_int_32()?))
	}

	pub fn and(&self, other: &Self) -> Option<Self> {
		if let (Self::UInteger(a), b) = (self, other) {
			return Some(Self::UInteger(a & b.to_uint_32()?));
		} else if let (a, Self::UInteger(b)) = (self, other) {
			return Some(Self::UInteger(a.to_uint_32()? & b));
		}
		Some(Self::Integer(self.to_int_32()? & other.to_int_32()?))
	}

	pub fn or(&self, other: &Self) -> Option<Self> {
		if let (Self::UInteger(a), b) = (self, other) {
			return Some(Self::UInteger(a | b.to_uint_32()?));
		} else if let (a, Self::UInteger(b)) = (self, other) {
			return Some(Self::UInteger(a.to_uint_32()? | b));
		}
		Some(Self::Integer(self.to_int_32()? | other.to_int_32()?))
	}

	pub fn fadd(&self, other: &Self) -> Option<Self> {
		Some(Self::Float(self.to_float()? + other.to_float()?))
	}

	pub fn fsub(&self, other: &Self) -> Option<Self> {
		Some(Self::Float(self.to_float()? - other.to_float()?))
	}

	pub fn fmult(&self, other: &Self) -> Option<Self> {
		Some(Self::Float(self.to_float()? * other.to_float()?))
	}

	pub fn fdiv(&self, other: &Self) -> Option<Self> {
		Some(Self::Float(self.to_float()? / other.to_float()?))
	}

	pub fn negate(&self) -> Option<Self> { Some(Self::Integer(-self.to_int_32()?)) }

	pub fn is_zero(&self) -> bool {
		match self {
			Self::Integer(0) => true,
			Self::UInteger(0) => true,
			Self::Float(num) => *num == 0.0,
			_ => false,
		}
	}
	pub fn is_one(&self) -> bool {
		match self {
			Self::Integer(1) => true,
			Self::UInteger(1) => true,
			Self::Float(num) => *num == 1.0,
			_ => false,
		}
	}
	pub fn comp(&self, other: &Self) -> Option<Self> {
		Some(match (self, other) {
			(Self::Integer(a), Self::Integer(b)) => Self::Integer(match a.cmp(b) {
				Ordering::Greater => 1,
				Ordering::Less => -1,
				Ordering::Equal => 0,
			}),
			(Self::UInteger(a), Self::UInteger(b)) => Self::UInteger(match a.cmp(b) {
				Ordering::Greater => 1,
				Ordering::Less => NEGATIVE_UINT,
				Ordering::Equal => 0,
			}),
			(Self::UInteger(a), b) => {
				Self::UInteger(match a.cmp(&b.to_uint_32()?) {
					Ordering::Greater => 1,
					Ordering::Less => NEGATIVE_UINT,
					Ordering::Equal => 0,
				})
			}
			(a, Self::UInteger(b)) => {
				Self::UInteger(match a.to_uint_32()?.cmp(b) {
					Ordering::Greater => 1,
					Ordering::Less => NEGATIVE_UINT,
					Ordering::Equal => 0,
				})
			}
			(Self::Float(a), Self::Float(b)) => Self::Float(match a.partial_cmp(b)? {
				Ordering::Greater => 1.0,
				Ordering::Less => -1.0,
				Ordering::Equal => 0.0,
			}),
			_ => {
				return None;
			}
		})
	}
	pub fn cmp_eq(&self, other: &Self) -> Option<Self> {
		Some(match (self, other) {
			(Self::Integer(a), Self::Integer(b)) => Self::Integer(if a == b { 1 } else { 0 }),
			(Self::UInteger(a), Self::UInteger(b)) => Self::UInteger(if a == b { 1 } else { 0 }),
			(Self::UInteger(a), b) | (b, Self::UInteger(a)) => {
				let b = b.to_uint_32()?;
				Self::UInteger(if *a == b { 1 } else { 0 })
			}
			(Self::Float(a), Self::Float(b)) => Self::Float(if a == b { 1.0 } else { 0.0 }),
			_ => {
				return None;
			}
		})
	}
	pub fn cmp_ne(&self, other: &Self) -> Option<Self> {
		Some(match (self, other) {
			(Self::Integer(a), Self::Integer(b)) => Self::Integer(if a != b { 1 } else { 0 }),
			(Self::UInteger(a), Self::UInteger(b)) => Self::UInteger(if a != b { 1 } else { 0 }),
			(Self::UInteger(a), b) | (b, Self::UInteger(a)) => {
				let b = b.to_uint_32()?;
				Self::UInteger(if *a != b { 1 } else { 0 })
			}
			(Self::Float(a), Self::Float(b)) => Self::Float(if a != b { 1.0 } else { 0.0 }),
			_ => {
				return None;
			}
		})
	}
	pub fn cmp_lt(&self, other: &Self) -> Option<Self> {
		Some(match (self, other) {
			(Self::Integer(a), Self::Integer(b)) => Self::Integer(if a < b { 1 } else { 0 }),
			(Self::UInteger(a), Self::UInteger(b)) => Self::UInteger(if a < b { 1 } else { 0 }),
			(Self::UInteger(a), b) | (b, Self::UInteger(a)) => {
				let b = b.to_uint_32()?;

				// if *a == NEGATIVE_UINT && b != NEGATIVE_UINT { return Some(Self::UInteger(1)); }

				Self::UInteger(if *a < b { 1 } else { 0 })
			}
			(a, Self::UInteger(b)) => {
				let a = a.to_uint_32()?;

				// if a == NEGATIVE_UINT && *b != NEGATIVE_UINT { return Some(Self::UInteger(1)); }

				Self::UInteger(if a < *b { 1 } else { 0 })
			}
			(Self::Float(a), Self::Float(b)) => Self::Float(if a < b { 1.0 } else { 0.0 }),
			_ => {
				return None;
			}
		})
	}
	pub fn cmp_le(&self, other: &Self) -> Option<Self> {
		Some(match (self, other) {
			(Self::Integer(a), Self::Integer(b)) => Self::Integer(if a <= b { 1 } else { 0 }),
			(Self::UInteger(a), Self::UInteger(b)) => Self::UInteger(if a <= b { 1 } else { 0 }),
			(Self::UInteger(a), b) => {
				// if *a == NEGATIVE_UINT { return Some(Self::UInteger(1)); }

				let b = b.to_uint_32()?;
				Self::UInteger(if *a <= b { 1 } else { 0 })
			}
			(a, Self::UInteger(b)) => {
				let a = a.to_uint_32()?;

				// if a == NEGATIVE_UINT { return Some(Self::UInteger(1)); }

				Self::UInteger(if a <= *b { 1 } else { 0 })
			}
			(Self::Float(a), Self::Float(b)) => Self::Float(if a <= b { 1.0 } else { 0.0 }),
			_ => {
				return None;
			}
		})
	}
	pub fn cmp_gt(&self, other: &Self) -> Option<Self> {
		Some(match (self, other) {
			(Self::Integer(a), Self::Integer(b)) => Self::Integer(if a > b { 1 } else { 0 }),
			(Self::UInteger(a), Self::UInteger(b)) => Self::UInteger(if a > b { 1 } else { 0 }),
			(Self::UInteger(a), b) => {
				let b = b.to_uint_32()?;

				// if *a == NEGATIVE_UINT { return Some(Self::UInteger(0)); }

				Self::UInteger(if *a > b { 1 } else { 0 })
			}
			(a, Self::UInteger(b)) => {
				let a = a.to_uint_32()?;

				// if a == NEGATIVE_UINT { return Some(Self::UInteger(0)); }

				Self::UInteger(if a > *b { 1 } else { 0 })
			}
			(Self::Float(a), Self::Float(b)) => Self::Float(if a > b { 1.0 } else { 0.0 }),
			_ => {
				return None;
			}
		})
	}
	pub fn cmp_ge(&self, other: &Self) -> Option<Self> {
		Some(match (self, other) {
			(Self::Integer(a), Self::Integer(b)) => Self::Integer(if a >= b { 1 } else { 0 }),
			(Self::UInteger(a), Self::UInteger(b)) => Self::UInteger(if a >= b { 1 } else { 0 }),
			(Self::UInteger(a), b) => {
				let b = b.to_uint_32()?;

				// if *a == NEGATIVE_UINT && b != NEGATIVE_UINT { return Some(Self::UInteger(0)); }

				Self::UInteger(if *a >= b { 1 } else { 0 })
			}
			(a, Self::UInteger(b)) => {
				let a = a.to_uint_32()?;

				// if a == NEGATIVE_UINT && *b != NEGATIVE_UINT { return Some(Self::UInteger(0)); }

				Self::UInteger(if a >= *b { 1 } else { 0 })
			}
			(Self::Float(a), Self::Float(b)) => Self::Float(if a >= b { 1.0 } else { 0.0 }),
			_ => {
				return None;
			}
		})
	}
}

impl Hash for Val {
	fn hash<H: hash::Hasher>(&self, state: &mut H) {
		discriminant(self).hash(state);
		match self {
			Self::Integer(int) => int.hash(state),
			Self::UInteger(int) => int.hash(state),
			Self::Float(float) => float.to_bits().hash(state),
			Self::Location(s) => s.hash(state),
			Self::String(s) => s.hash(state),
			Self::Null => {}
		}
	}
}
impl PartialEq for Val {
	fn eq(&self, other: &Self) -> bool {
		match (self, other) {
			(Self::Integer(a), Self::Integer(b)) => a.eq(b),
			(Self::Float(a), Self::Float(b)) => a.to_bits().eq(&b.to_bits()),
			(Self::Location(a), Self::Location(b)) => a.eq(b),
			_ => false,
		}
	}
}
impl Eq for Val {}
impl FromStr for Val {
	type Err = &'static str;
	fn from_str(s: &str) -> Result<Self, Self::Err> {
		Ok(if s.chars().all(|c| c.is_numeric() || c == '-') {
			let mut x = s.parse::<isize>().map_err(|_| "failed to parse isize")?;
			// TODO: confirm
			// This conversion should always do the correct thing...
			let x = x as i32;
			Val::Integer(x)
		} else {
			Val::Location(s.to_string())
		})
	}
}
impl fmt::Display for Val {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			Val::Integer(int) => int.fmt(f),
			Val::UInteger(int) => int.fmt(f),
			Val::Float(flt) => flt.fmt(f),
			Val::Location(loc) => loc.fmt(f),
			Val::String(s) => s.fmt(f),
			Val::Null => write!(f, "null"),
		}
	}
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Reg {
	Var(usize),
	Phi(usize, usize),
}

impl FromStr for Reg {
	type Err = &'static str;
	fn from_str(s: &str) -> Result<Self, Self::Err> {
		if !s.starts_with("%vr") {
			return Err("register must start with %vr[num]");
		}
		Ok(Reg::Var(
			s.split("%vr")
				.last()
				.ok_or("no register number found")?
				.parse::<usize>()
				.map_err(|_| "`Reg` parse error")?,
		))
	}
}
impl fmt::Display for Reg {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			Reg::Var(num) if unsafe { crate::SSA } => write!(f, "%vr{}", num),
			Reg::Phi(num, subs) if unsafe { crate::SSA } => {
				write!(f, "%vr{}_{}", num, subs)
			}
			// Reg::Phi(num, subs) => write!(f, "%vr{}_{}", num, subs),
			Reg::Var(num) | Reg::Phi(num, ..) => write!(f, "%vr{}", num),
		}
	}
}

impl Reg {
	pub fn as_phi(&mut self, phi_id: usize) {
		if let Reg::Var(curr) = self {
			*self = Reg::Phi(*curr, phi_id);
		} else if let Reg::Phi(_, old) = self {
			*old = phi_id;
		}
	}

	pub fn as_usize(&self) -> usize {
		if let Reg::Var(curr) = self {
			*curr
		} else {
			unreachable!("not just Reg::Var in hurr {:?}", self)
		}
	}

	pub fn remove_phi(&mut self) {
		if let Reg::Phi(reg, ..) = self {
			*self = Reg::Var(*reg)
		}
	}
	pub fn to_register(self) -> Reg {
		if let Reg::Phi(reg, ..) = self {
			Reg::Var(reg)
		} else {
			self
		}
	}
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Loc(pub String);

impl Loc {
	pub fn as_str(&self) -> &str { self.0.as_str() }
}
impl FromStr for Loc {
	type Err = &'static str;

	fn from_str(s: &str) -> Result<Self, Self::Err> { Ok(Self(s.to_string())) }
}
impl fmt::Display for Loc {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{}", self.0) }
}

#[rustfmt::skip]
#[allow(clippy::upper_case_acronyms)]
#[derive(Clone, Debug)]
pub enum Instruction {
	// Integer arithmetic operations
	/// %r => %r `i2i`
	I2I { src: Reg, dst: Reg },
	/// %r + %r => %r `add`
	Add { src_a: Reg, src_b: Reg, dst: Reg },
	/// %r - %r => %r `sub`
	Sub { src_a: Reg, src_b: Reg, dst: Reg },
	/// %r * %r => %r `mult`
	Mult { src_a: Reg, src_b: Reg, dst: Reg },
	#[allow(unused)]
	/// %r / %r => %r `div`
	Div { src_a: Reg, src_b: Reg, dst: Reg },
	/// %r << %r => %r `lshift`
	LShift { src_a: Reg, src_b: Reg, dst: Reg },
	/// %r >> %r => %r `rshift`
	RShift { src_a: Reg, src_b: Reg, dst: Reg },
	/// %r % %r => %r `mod`
	Mod { src_a: Reg, src_b: Reg, dst: Reg },
	/// %r && %r => %r `and`
	And { src_a: Reg, src_b: Reg, dst: Reg },
	/// %r || %r => %r `or`
	Or { src_a: Reg, src_b: Reg, dst: Reg },
	/// !%r => %r `not`
	Not { src: Reg, dst: Reg },

	// Immediate integer operations
	/// %r + c => %r `addI`
	ImmAdd { src: Reg, konst: Val, dst: Reg },
	/// %r - c => %r `subI`
	ImmSub { src: Reg, konst: Val, dst: Reg },
	/// %r * c => %r `multI`
	ImmMult { src: Reg, konst: Val, dst: Reg },
	/// %r << c => %r `lshiftI`
	ImmLShift { src: Reg, konst: Val, dst: Reg },
	/// %r >> c => %r `rshftI`
	ImmRShift { src: Reg, konst: Val, dst: Reg },

	// Integer memory operations
	/// c => %r `loadI`
	ImmLoad { src: Val, dst: Reg },
	/// %r => %r `load`
	Load { src: Reg, dst: Reg },
	/// (%r + c) => %r `loadAI`
	///
	/// Where `add + src` is the location on the stack to load into `dst`.
	LoadAddImm { src: Reg, add: Val, dst: Reg },
	/// (%r + %r) => %r `loadAO`
	LoadAdd { src: Reg, add: Reg, dst: Reg },
	/// %r => %r `store`
	Store { src: Reg, dst: Reg },
	/// %r => (%r + c) `storeAI`
	///
	/// Where `add + dst` is the location on the stack to store `src`.
	StoreAddImm { src: Reg, add: Val, dst: Reg },
	/// %r => (%r + %r) `storeAO`
	StoreAdd { src: Reg, add: Reg, dst: Reg },

	// Comparison operations
	/// cmp_Lt %r, %r => %r
	CmpLT { a: Reg, b: Reg, dst: Reg },
	CmpLE { a: Reg, b: Reg, dst: Reg },
	CmpGT { a: Reg, b: Reg, dst: Reg },
	CmpGE { a: Reg, b: Reg, dst: Reg },
	CmpEQ { a: Reg, b: Reg, dst: Reg },
	CmpNE { a: Reg, b: Reg, dst: Reg },
	Comp { a: Reg, b: Reg, dst: Reg },
	TestEQ { test: Reg, dst: Reg },
	TestNE { test: Reg, dst: Reg },
	TestGT { test: Reg, dst: Reg },
	TestGE { test: Reg, dst: Reg },
	TestLT { test: Reg, dst: Reg },
	TestLE { test: Reg, dst: Reg },

	// Branches
	/// jump to lable `jumpI`
	ImmJump(Loc),
	/// jump %r `jump`
	Jump(Reg),
	/// Call instruction, includes arguments.
	/// `call name %r, %r
	Call { name: String, args: Vec<Reg> },
	/// Call instruction, includes arguments and return register.
	/// `call name %r, %r => %r
	ImmCall { name: String, args: Vec<Reg>, ret: Reg },
	/// Call instruction, includes arguments and return register.
	/// `call name %r, %r => %r
	ImmRCall { reg: Reg, args: Vec<Reg>, ret: Reg },
	/// `ret`
	Ret,
	/// Return a value in a register.
	/// `iret %r`
	ImmRet(Reg),
	/// cbr %r -> label `cbr` conditional break if tree
	CbrT { cond: Reg, loc: Loc },
	/// cbrne %r -> label `cbrne` conditional break if false
	CbrF { cond: Reg, loc: Loc },
	CbrLT { a: Reg, b: Reg, loc: Loc },
	CbrLE { a: Reg, b: Reg, loc: Loc },
	CbrGT { a: Reg, b: Reg, loc: Loc },
	CbrGE { a: Reg, b: Reg, loc: Loc },
	CbrEQ { a: Reg, b: Reg, loc: Loc },
	CbrNE { a: Reg, b: Reg, loc: Loc },

	// Unsigned operations
	CmpuLT { a: Reg, b: Reg, dst: Reg },
	CmpuLE { a: Reg, b: Reg, dst: Reg },
	CmpuGT { a: Reg, b: Reg, dst: Reg },
	CmpuGE { a: Reg, b: Reg, dst: Reg },
	Compu { a: Reg, b: Reg, dst: Reg },
	TestuGT { test: Reg, dst: Reg },
	TestuGE { test: Reg, dst: Reg },
	TestuLT { test: Reg, dst: Reg },
	TestuLE { test: Reg, dst: Reg },
	CbruLT { a: Reg, b: Reg, loc: Loc },
	CbruLE { a: Reg, b: Reg, loc: Loc },
	CbruGT { a: Reg, b: Reg, loc: Loc },
	CbruGE { a: Reg, b: Reg, loc: Loc },
	RShiftu { src_a: Reg, src_b: Reg, dst: Reg },
	ImmRShiftu { src: Reg, konst: Val, dst: Reg },


	// Floating point arithmetic
	/// `f2i`
	F2I { src: Reg, dst: Reg },
	/// `i2f`
	I2F { src: Reg, dst: Reg },
	/// `f2f`
	F2F { src: Reg, dst: Reg },
	/// `fadd`
	FAdd { src_a: Reg, src_b: Reg, dst: Reg },
	/// `fsub`
	FSub { src_a: Reg, src_b: Reg, dst: Reg },
	/// `fmult`
	FMult { src_a: Reg, src_b: Reg, dst: Reg },
	/// `fdiv`
	FDiv { src_a: Reg, src_b: Reg, dst: Reg },
	/// `fcomp`
	FComp { src_a: Reg, src_b: Reg, dst: Reg },
	/// `fload`
	FLoad { src: Reg, dst: Reg },
	/// `floadAI`
	FLoadAddImm { src: Reg, add: Val, dst: Reg },
	/// `floadAO`
	FLoadAdd { src: Reg, add: Reg, dst: Reg },

	// I/O operations
	/// `fread %r` where r is a float target.
	FRead(Reg),
	/// `fread %r` where r is an int target.
	IRead(Reg),
	/// `fread %r` where r is a float source.
	FWrite(Reg),
	/// `fread %r` where r is an integer source.
	IWrite(Reg),
	/// `fread %r` where r is a null terminated string source.
	SWrite(Reg),
	/// `putchar %r` where r is a int but written as ascii.
	PutChar(Reg),

	// Malloc - Free - Realloc
	/// `malloc %r => %r` where arg `r` is an int for the size and return `r` is the
	/// register that hold the address.
	Malloc { size: Reg, dst: Reg },
	/// `free %r` where `r` is the register to be freed, must be valid.
	Free(Reg),
	/// `realloc %r, %r => %r` where first `r` is the old address, second `r` is an int for the size
	/// and `r` is the register that hold the address.
	Realloc { src: Reg, size: Reg, dst: Reg },

	// Stack operations
	/// `push`
	Push(Val),
	/// `pushr`
	PushR(Reg),
	/// `pop`
	Pop,
	// Pseudo operations
	Data,
	Text,
	Frame { name: String, size: usize, params: Vec<Reg> },
	Global { name: String, size: usize, align: usize, content: Vec<Val> },
	Array { name: String, size: usize, content: Vec<Val> },
	String { name: String, content: String },
	Float { name: String, content: f64 },

	// TODO: hmm should this not be
	/// Labeled block.
	Label(String),

	/// This is a signal to the output generator to skip this instruction.
	Skip(String),
	// TODO: use something that doesn't make this variant huge
	/// Phi nodes that are inserted when blocks are converted to pruned SSA.
	Phi(Reg, BTreeSet<usize>, Option<usize>),
}

impl Hash for Instruction {
	fn hash<H: hash::Hasher>(&self, state: &mut H) {
		let variant = discriminant(self);
		match self {
			Instruction::FLoad { src, dst }
			| Instruction::F2I { src, dst }
			| Instruction::I2F { src, dst }
			| Instruction::F2F { src, dst }
			| Instruction::Store { src, dst }
			| Instruction::Load { src, dst }
			| Instruction::I2I { src, dst }
			| Instruction::Not { src, dst } => (src, dst, variant).hash(state),

			Instruction::Add { src_a, src_b, dst }
			| Instruction::Sub { src_a, src_b, dst }
			| Instruction::Mult { src_a, src_b, dst }
			| Instruction::Div { src_a, src_b, dst }
			| Instruction::LShift { src_a, src_b, dst }
			| Instruction::RShift { src_a, src_b, dst }
			| Instruction::Mod { src_a, src_b, dst }
			| Instruction::And { src_a, src_b, dst }
			| Instruction::Or { src_a, src_b, dst } => (src_a, src_b, dst, variant).hash(state),

			Instruction::ImmAdd { src, konst, dst }
			| Instruction::ImmSub { src, konst, dst }
			| Instruction::ImmMult { src, konst, dst }
			| Instruction::ImmLShift { src, konst, dst }
			| Instruction::ImmRShift { src, konst, dst } => (src, konst, dst, variant).hash(state),

			Instruction::ImmLoad { src, dst } => (src, dst, variant).hash(state),

			Instruction::LoadAddImm { src, add, dst }
			| Instruction::StoreAddImm { src, add, dst } => (src, add, dst, variant).hash(state),
			Instruction::LoadAdd { src, add, dst } | Instruction::StoreAdd { src, add, dst } => {
				(src, add, dst, variant).hash(state)
			}
			Instruction::CmpLT { a, b, dst }
			| Instruction::CmpLE { a, b, dst }
			| Instruction::CmpGT { a, b, dst }
			| Instruction::CmpGE { a, b, dst }
			| Instruction::CmpEQ { a, b, dst }
			| Instruction::CmpNE { a, b, dst }
			| Instruction::Comp { a, b, dst }
			// unsigned
			| Instruction::CmpuGE { a, b, dst }
			| Instruction::CmpuGT { a, b, dst }
			| Instruction::CmpuLE { a, b, dst }
			| Instruction::CmpuLT { a, b, dst }
			| Instruction::Compu { a, b, dst } => (a, b, dst, variant).hash(state),
			Instruction::TestEQ { test, dst }
			| Instruction::TestNE { test, dst }
			| Instruction::TestGT { test, dst }
			| Instruction::TestGE { test, dst }
			| Instruction::TestLT { test, dst }
			| Instruction::TestLE { test, dst }
			// unsigned
			| Instruction::TestuGE { test, dst }
			| Instruction::TestuGT { test, dst }
			| Instruction::TestuLE { test, dst }
			| Instruction::TestuLT { test, dst } => (test, dst, variant).hash(state),
			Instruction::ImmJump(s) => (s, variant).hash(state),
			Instruction::Jump(s) => (s, variant).hash(state),
			Instruction::Call { name, args } => (name, args, variant).hash(state),
			Instruction::ImmCall { name, args, ret } => (name, args, ret, variant).hash(state),
			Instruction::ImmRCall { reg, args, ret } => (reg, args, ret, variant).hash(state),
			Instruction::ImmRet(s) => (s, variant).hash(state),
			Instruction::CbrT { cond, loc } | Instruction::CbrF { cond, loc } => {
				(cond, loc, variant).hash(state)
			}
			Instruction::CbrLT { a, b, loc }
			| Instruction::CbrLE { a, b, loc }
			| Instruction::CbrGT { a, b, loc }
			| Instruction::CbrGE { a, b, loc }
			| Instruction::CbrEQ { a, b, loc }
			| Instruction::CbrNE { a, b, loc }
			// unsigned
			| Instruction::CbruGE { a, b, loc }
			| Instruction::CbruGT { a, b, loc }
			| Instruction::CbruLE { a, b, loc }
			| Instruction::CbruLT { a, b, loc } => (a, b, loc, variant).hash(state),

			Instruction::RShiftu { src_a, src_b, dst } => (src_a, src_b, dst, variant).hash(state),
			Instruction::ImmRShiftu { src, konst, dst } => (src, konst, dst, variant).hash(state),

			Instruction::FAdd { src_a, src_b, dst }
			| Instruction::FSub { src_a, src_b, dst }
			| Instruction::FMult { src_a, src_b, dst }
			| Instruction::FDiv { src_a, src_b, dst }
			| Instruction::FComp { src_a, src_b, dst } => (src_a, src_b, dst, variant).hash(state),
			Instruction::FLoadAddImm { src, add, dst } => (src, add, dst, variant).hash(state),
			Instruction::FLoadAdd { src, add, dst } => (src, add, dst, variant).hash(state),
			Instruction::FRead(s)
			| Instruction::IRead(s)
			| Instruction::FWrite(s)
			| Instruction::IWrite(s)
			| Instruction::PutChar(s)
			| Instruction::SWrite(s) => (s, variant).hash(state),
			Instruction::Malloc { size, dst } => (size, dst, variant).hash(state),
			Instruction::Free(src) => (src, variant).hash(state),
			Instruction::Realloc { src, size, dst } => (src, size, dst, variant).hash(state),
			Instruction::Push(s) => (s, variant).hash(state),
			Instruction::PushR(s) => (s, variant).hash(state),
			Instruction::Frame { name, size, params } => (name, size, params, variant).hash(state),
			Instruction::Global { name, size, align, content } => (name, size, align, content, variant).hash(state),
			Instruction::Array { name, size, content } => (name, size, content).hash(state),
			Instruction::String { name, content } => (name, content, variant).hash(state),
			Instruction::Float { name, content } => (name, content.to_bits(), variant).hash(state),
			Instruction::Label(s) => (variant, s).hash(state),
			Instruction::Phi(r, set, subs) => (r, set, subs, variant).hash(state),
			Instruction::Ret => variant.hash(state),
			Instruction::Pop => variant.hash(state),
			Instruction::Data => variant.hash(state),
			Instruction::Text => variant.hash(state),
			Instruction::Skip(_) => unreachable!("shouldn't hash skipped instructions"),
		};
	}
}
impl PartialEq for Instruction {
	fn eq(&self, other: &Self) -> bool {
		match (self, other) {
			(Self::I2I { src: l_src, dst: l_dst }, Self::I2I { src: r_src, dst: r_dst }) => {
				l_src == r_src && l_dst == r_dst
			}
			(
				Self::Add { src_a: l_src_a, src_b: l_src_b, dst: l_dst },
				Self::Add { src_a: r_src_a, src_b: r_src_b, dst: r_dst },
			) => l_src_a == r_src_a && l_src_b == r_src_b && l_dst == r_dst,
			(
				Self::Sub { src_a: l_src_a, src_b: l_src_b, dst: l_dst },
				Self::Sub { src_a: r_src_a, src_b: r_src_b, dst: r_dst },
			) => l_src_a == r_src_a && l_src_b == r_src_b && l_dst == r_dst,
			(
				Self::Mult { src_a: l_src_a, src_b: l_src_b, dst: l_dst },
				Self::Mult { src_a: r_src_a, src_b: r_src_b, dst: r_dst },
			) => l_src_a == r_src_a && l_src_b == r_src_b && l_dst == r_dst,
			(
				Self::LShift { src_a: l_src_a, src_b: l_src_b, dst: l_dst },
				Self::LShift { src_a: r_src_a, src_b: r_src_b, dst: r_dst },
			) => l_src_a == r_src_a && l_src_b == r_src_b && l_dst == r_dst,
			(
				Self::RShift { src_a: l_src_a, src_b: l_src_b, dst: l_dst },
				Self::RShift { src_a: r_src_a, src_b: r_src_b, dst: r_dst },
			) => l_src_a == r_src_a && l_src_b == r_src_b && l_dst == r_dst,
			(
				Self::Mod { src_a: l_src_a, src_b: l_src_b, dst: l_dst },
				Self::Mod { src_a: r_src_a, src_b: r_src_b, dst: r_dst },
			) => l_src_a == r_src_a && l_src_b == r_src_b && l_dst == r_dst,
			(
				Self::And { src_a: l_src_a, src_b: l_src_b, dst: l_dst },
				Self::And { src_a: r_src_a, src_b: r_src_b, dst: r_dst },
			) => l_src_a == r_src_a && l_src_b == r_src_b && l_dst == r_dst,
			(
				Self::Or { src_a: l_src_a, src_b: l_src_b, dst: l_dst },
				Self::Or { src_a: r_src_a, src_b: r_src_b, dst: r_dst },
			) => l_src_a == r_src_a && l_src_b == r_src_b && l_dst == r_dst,
			(Self::Not { src: l_src, dst: l_dst }, Self::Not { src: r_src, dst: r_dst }) => {
				l_src == r_src && l_dst == r_dst
			}
			(
				Self::ImmAdd { src: l_src, konst: l_konst, dst: l_dst },
				Self::ImmAdd { src: r_src, konst: r_konst, dst: r_dst },
			) => l_src == r_src && l_konst == r_konst && l_dst == r_dst,
			(
				Self::ImmSub { src: l_src, konst: l_konst, dst: l_dst },
				Self::ImmSub { src: r_src, konst: r_konst, dst: r_dst },
			) => l_src == r_src && l_konst == r_konst && l_dst == r_dst,
			(
				Self::ImmMult { src: l_src, konst: l_konst, dst: l_dst },
				Self::ImmMult { src: r_src, konst: r_konst, dst: r_dst },
			) => l_src == r_src && l_konst == r_konst && l_dst == r_dst,
			(
				Self::ImmLShift { src: l_src, konst: l_konst, dst: l_dst },
				Self::ImmLShift { src: r_src, konst: r_konst, dst: r_dst },
			) => l_src == r_src && l_konst == r_konst && l_dst == r_dst,
			(
				Self::ImmRShift { src: l_src, konst: l_konst, dst: l_dst },
				Self::ImmRShift { src: r_src, konst: r_konst, dst: r_dst },
			) => l_src == r_src && l_konst == r_konst && l_dst == r_dst,
			(
				Self::ImmLoad { src: l_src, dst: l_dst },
				Self::ImmLoad { src: r_src, dst: r_dst },
			) => l_src == r_src && l_dst == r_dst,
			(Self::Load { src: l_src, dst: l_dst }, Self::Load { src: r_src, dst: r_dst }) => {
				l_src == r_src && l_dst == r_dst
			}
			(
				Self::LoadAddImm { src: l_src, add: l_add, dst: l_dst },
				Self::LoadAddImm { src: r_src, add: r_add, dst: r_dst },
			) => l_src == r_src && l_add == r_add && l_dst == r_dst,
			(
				Self::LoadAdd { src: l_src, add: l_add, dst: l_dst },
				Self::LoadAdd { src: r_src, add: r_add, dst: r_dst },
			) => l_src == r_src && l_add == r_add && l_dst == r_dst,
			(Self::Store { src: l_src, dst: l_dst }, Self::Store { src: r_src, dst: r_dst }) => {
				l_src == r_src && l_dst == r_dst
			}
			(
				Self::StoreAddImm { src: l_src, add: l_add, dst: l_dst },
				Self::StoreAddImm { src: r_src, add: r_add, dst: r_dst },
			) => l_src == r_src && l_add == r_add && l_dst == r_dst,
			(
				Self::StoreAdd { src: l_src, add: l_add, dst: l_dst },
				Self::StoreAdd { src: r_src, add: r_add, dst: r_dst },
			) => l_src == r_src && l_add == r_add && l_dst == r_dst,
			(
				Self::CmpLT { a: l_a, b: l_b, dst: l_dst },
				Self::CmpLT { a: r_a, b: r_b, dst: r_dst },
			) => l_a == r_a && l_b == r_b && l_dst == r_dst,
			(
				Self::CmpLE { a: l_a, b: l_b, dst: l_dst },
				Self::CmpLE { a: r_a, b: r_b, dst: r_dst },
			) => l_a == r_a && l_b == r_b && l_dst == r_dst,
			(
				Self::CmpGT { a: l_a, b: l_b, dst: l_dst },
				Self::CmpGT { a: r_a, b: r_b, dst: r_dst },
			) => l_a == r_a && l_b == r_b && l_dst == r_dst,
			(
				Self::CmpGE { a: l_a, b: l_b, dst: l_dst },
				Self::CmpGE { a: r_a, b: r_b, dst: r_dst },
			) => l_a == r_a && l_b == r_b && l_dst == r_dst,
			(
				Self::CmpEQ { a: l_a, b: l_b, dst: l_dst },
				Self::CmpEQ { a: r_a, b: r_b, dst: r_dst },
			) => l_a == r_a && l_b == r_b && l_dst == r_dst,
			(
				Self::CmpNE { a: l_a, b: l_b, dst: l_dst },
				Self::CmpNE { a: r_a, b: r_b, dst: r_dst },
			) => l_a == r_a && l_b == r_b && l_dst == r_dst,
			(
				Self::Comp { a: l_a, b: l_b, dst: l_dst },
				Self::Comp { a: r_a, b: r_b, dst: r_dst },
			) => l_a == r_a && l_b == r_b && l_dst == r_dst,
			(
				Self::TestEQ { test: l_test, dst: l_dst },
				Self::TestEQ { test: r_test, dst: r_dst },
			) => l_test == r_test && l_dst == r_dst,
			(
				Self::TestNE { test: l_test, dst: l_dst },
				Self::TestNE { test: r_test, dst: r_dst },
			) => l_test == r_test && l_dst == r_dst,
			(
				Self::TestGT { test: l_test, dst: l_dst },
				Self::TestGT { test: r_test, dst: r_dst },
			) => l_test == r_test && l_dst == r_dst,
			(
				Self::TestGE { test: l_test, dst: l_dst },
				Self::TestGE { test: r_test, dst: r_dst },
			) => l_test == r_test && l_dst == r_dst,
			(
				Self::TestLT { test: l_test, dst: l_dst },
				Self::TestLT { test: r_test, dst: r_dst },
			) => l_test == r_test && l_dst == r_dst,
			(
				Self::TestLE { test: l_test, dst: l_dst },
				Self::TestLE { test: r_test, dst: r_dst },
			) => l_test == r_test && l_dst == r_dst,

			// Unsigned
			(
				Self::CmpuGE { a: l_a, b: l_b, dst: l_dst },
				Self::CmpuGE { a: r_a, b: r_b, dst: r_dst },
			) => l_a == r_a && l_b == r_b && l_dst == r_dst,
			(
				Self::CmpuGT { a: l_a, b: l_b, dst: l_dst },
				Self::CmpuGT { a: r_a, b: r_b, dst: r_dst },
			) => l_a == r_a && l_b == r_b && l_dst == r_dst,
			(
				Self::CmpuLE { a: l_a, b: l_b, dst: l_dst },
				Self::CmpuLE { a: r_a, b: r_b, dst: r_dst },
			) => l_a == r_a && l_b == r_b && l_dst == r_dst,
			(
				Self::CmpuLT { a: l_a, b: l_b, dst: l_dst },
				Self::CmpuLT { a: r_a, b: r_b, dst: r_dst },
			) => l_a == r_a && l_b == r_b && l_dst == r_dst,
			(
				Self::CbruGE { a: l_a, b: l_b, loc: l_loc },
				Self::CbruGE { a: r_a, b: r_b, loc: r_loc },
			) => l_a == r_a && l_b == r_b && l_loc == r_loc,
			(
				Self::CbruGT { a: l_a, b: l_b, loc: l_loc },
				Self::CbruGT { a: r_a, b: r_b, loc: r_loc },
			) => l_a == r_a && l_b == r_b && l_loc == r_loc,
			(
				Self::CbruLE { a: l_a, b: l_b, loc: l_loc },
				Self::CbruLE { a: r_a, b: r_b, loc: r_loc },
			) => l_a == r_a && l_b == r_b && l_loc == r_loc,
			(
				Self::CbruLT { a: l_a, b: l_b, loc: l_loc },
				Self::CbruLT { a: r_a, b: r_b, loc: r_loc },
			) => l_a == r_a && l_b == r_b && l_loc == r_loc,
			(
				Self::TestuGE { test: l_test, dst: l_dst },
				Self::TestuGE { test: r_test, dst: r_dst },
			) => l_test == r_test && l_dst == r_dst,
			(
				Self::TestuGT { test: l_test, dst: l_dst },
				Self::TestuGT { test: r_test, dst: r_dst },
			) => l_test == r_test && l_dst == r_dst,
			(
				Self::TestuLE { test: l_test, dst: l_dst },
				Self::TestuLE { test: r_test, dst: r_dst },
			) => l_test == r_test && l_dst == r_dst,
			(
				Self::TestuLT { test: l_test, dst: l_dst },
				Self::TestuLT { test: r_test, dst: r_dst },
			) => l_test == r_test && l_dst == r_dst,
			(
				Self::Compu { a: l_a, b: l_b, dst: l_dst },
				Self::Compu { a: r_a, b: r_b, dst: r_dst },
			) => l_a == r_a && l_b == r_b && l_dst == r_dst,
			(
				Self::RShiftu { src_a: l_a, src_b: l_b, dst: l_dst },
				Self::RShiftu { src_a: r_a, src_b: r_b, dst: r_dst },
			) => l_a == r_a && l_b == r_b && l_dst == r_dst,
			(
				Self::ImmRShiftu { src: l_a, konst: l_b, dst: l_dst },
				Self::ImmRShiftu { src: r_a, konst: r_b, dst: r_dst },
			) => l_a == r_a && l_b == r_b && l_dst == r_dst,

			(Self::ImmJump(l0), Self::ImmJump(r0)) => l0 == r0,
			(Self::Jump(l0), Self::Jump(r0)) => l0 == r0,
			(
				Self::Call { name: l_name, args: l_args },
				Self::Call { name: r_name, args: r_args },
			) => l_name == r_name && l_args == r_args,
			(
				Self::ImmCall { name: l_name, args: l_args, ret: l_ret },
				Self::ImmCall { name: r_name, args: r_args, ret: r_ret },
			) => l_name == r_name && l_args == r_args && l_ret == r_ret,
			(
				Self::ImmRCall { reg: l_reg, args: l_args, ret: l_ret },
				Self::ImmRCall { reg: r_reg, args: r_args, ret: r_ret },
			) => l_reg == r_reg && l_args == r_args && l_ret == r_ret,
			(Self::ImmRet(l0), Self::ImmRet(r0)) => l0 == r0,
			(Self::CbrT { cond: l_cond, loc: l_loc }, Self::CbrT { cond: r_cond, loc: r_loc }) => {
				l_cond == r_cond && l_loc == r_loc
			}
			(Self::CbrF { cond: l_cond, loc: l_loc }, Self::CbrF { cond: r_cond, loc: r_loc }) => {
				l_cond == r_cond && l_loc == r_loc
			}
			(
				Self::CbrLT { a: l_a, b: l_b, loc: l_loc },
				Self::CbrLT { a: r_a, b: r_b, loc: r_loc },
			) => l_a == r_a && l_b == r_b && l_loc == r_loc,
			(
				Self::CbrLE { a: l_a, b: l_b, loc: l_loc },
				Self::CbrLE { a: r_a, b: r_b, loc: r_loc },
			) => l_a == r_a && l_b == r_b && l_loc == r_loc,
			(
				Self::CbrGT { a: l_a, b: l_b, loc: l_loc },
				Self::CbrGT { a: r_a, b: r_b, loc: r_loc },
			) => l_a == r_a && l_b == r_b && l_loc == r_loc,
			(
				Self::CbrGE { a: l_a, b: l_b, loc: l_loc },
				Self::CbrGE { a: r_a, b: r_b, loc: r_loc },
			) => l_a == r_a && l_b == r_b && l_loc == r_loc,
			(
				Self::CbrEQ { a: l_a, b: l_b, loc: l_loc },
				Self::CbrEQ { a: r_a, b: r_b, loc: r_loc },
			) => l_a == r_a && l_b == r_b && l_loc == r_loc,
			(
				Self::CbrNE { a: l_a, b: l_b, loc: l_loc },
				Self::CbrNE { a: r_a, b: r_b, loc: r_loc },
			) => l_a == r_a && l_b == r_b && l_loc == r_loc,
			(Self::F2I { src: l_src, dst: l_dst }, Self::F2I { src: r_src, dst: r_dst }) => {
				l_src == r_src && l_dst == r_dst
			}
			(Self::I2F { src: l_src, dst: l_dst }, Self::I2F { src: r_src, dst: r_dst }) => {
				l_src == r_src && l_dst == r_dst
			}
			(Self::F2F { src: l_src, dst: l_dst }, Self::F2F { src: r_src, dst: r_dst }) => {
				l_src == r_src && l_dst == r_dst
			}
			(
				Self::FAdd { src_a: l_src_a, src_b: l_src_b, dst: l_dst },
				Self::FAdd { src_a: r_src_a, src_b: r_src_b, dst: r_dst },
			) => l_src_a == r_src_a && l_src_b == r_src_b && l_dst == r_dst,
			(
				Self::FSub { src_a: l_src_a, src_b: l_src_b, dst: l_dst },
				Self::FSub { src_a: r_src_a, src_b: r_src_b, dst: r_dst },
			) => l_src_a == r_src_a && l_src_b == r_src_b && l_dst == r_dst,
			(
				Self::FMult { src_a: l_src_a, src_b: l_src_b, dst: l_dst },
				Self::FMult { src_a: r_src_a, src_b: r_src_b, dst: r_dst },
			) => l_src_a == r_src_a && l_src_b == r_src_b && l_dst == r_dst,
			(
				Self::FDiv { src_a: l_src_a, src_b: l_src_b, dst: l_dst },
				Self::FDiv { src_a: r_src_a, src_b: r_src_b, dst: r_dst },
			) => l_src_a == r_src_a && l_src_b == r_src_b && l_dst == r_dst,
			(
				Self::FComp { src_a: l_src_a, src_b: l_src_b, dst: l_dst },
				Self::FComp { src_a: r_src_a, src_b: r_src_b, dst: r_dst },
			) => l_src_a == r_src_a && l_src_b == r_src_b && l_dst == r_dst,
			(Self::FLoad { src: l_src, dst: l_dst }, Self::FLoad { src: r_src, dst: r_dst }) => {
				l_src == r_src && l_dst == r_dst
			}
			(
				Self::FLoadAddImm { src: l_src, add: l_add, dst: l_dst },
				Self::FLoadAddImm { src: r_src, add: r_add, dst: r_dst },
			) => l_src == r_src && l_add == r_add && l_dst == r_dst,
			(
				Self::FLoadAdd { src: l_src, add: l_add, dst: l_dst },
				Self::FLoadAdd { src: r_src, add: r_add, dst: r_dst },
			) => l_src == r_src && l_add == r_add && l_dst == r_dst,
			(Self::FRead(l0), Self::FRead(r0)) => l0 == r0,
			(Self::IRead(l0), Self::IRead(r0)) => l0 == r0,
			(Self::FWrite(l0), Self::FWrite(r0)) => l0 == r0,
			(Self::IWrite(l0), Self::IWrite(r0)) => l0 == r0,
			(Self::SWrite(l0), Self::SWrite(r0)) => l0 == r0,
			(Self::PutChar(l0), Self::PutChar(r0)) => l0 == r0,
			(
				Self::Malloc { size: size_a, dst: dst_a },
				Self::Malloc { size: size_b, dst: dst_b },
			) => size_a == size_b && dst_a == dst_b,
			(Self::Free(a), Self::Free(b)) => a == b,
			(
				Self::Realloc { src: src_a, size: size_a, dst: dst_a },
				Self::Realloc { src: src_b, size: size_b, dst: dst_b },
			) => src_a == src_b && size_a == size_b && dst_a == dst_b,
			(Self::Push(l0), Self::Push(r0)) => l0 == r0,
			(Self::PushR(l0), Self::PushR(r0)) => l0 == r0,
			(
				Self::Frame { name: l_name, size: l_size, params: l_params },
				Self::Frame { name: r_name, size: r_size, params: r_params },
			) => l_name == r_name && l_size == r_size && l_params == r_params,
			(
				Self::Global { name: l_name, size: l_size, align: l_align, content: l_cont },
				Self::Global { name: r_name, size: r_size, align: r_align, content: r_cont },
			) => l_name == r_name && l_size == r_size && l_align == r_align && l_cont == r_cont,
			(
				Self::Array { name: l_name, size: l_size, content: l_content },
				Self::Array { name: r_name, size: r_size, content: r_content },
			) => l_name == r_name && l_size == r_size && l_content == r_content,
			(
				Self::String { name: l_name, content: l_content },
				Self::String { name: r_name, content: r_content },
			) => l_name == r_name && l_content == r_content,
			(
				Self::Float { name: l_name, content: l_content },
				Self::Float { name: r_name, content: r_content },
			) => l_name == r_name && l_content.to_bits() == r_content.to_bits(),
			(Self::Label(l0), Self::Label(r0)) => l0 == r0,
			// Unit variants
			_ => core::mem::discriminant(self) == core::mem::discriminant(other),
		}
	}
}
impl Eq for Instruction {}
impl fmt::Display for Instruction {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			Self::FLoad { src, dst }
			| Self::F2I { src, dst }
			| Self::I2F { src, dst }
			| Self::F2F { src, dst }
			| Self::I2I { src, dst }
			| Self::Not { src, dst }
			| Self::Load { src, dst }
			| Self::Store { src, dst } => {
				writeln!(f, "    {} {} => {}", self.inst_name(), src, dst)
			}
			Self::Add { src_a, src_b, dst }
			| Self::Sub { src_a, src_b, dst }
			| Self::Mult { src_a, src_b, dst }
			| Self::Div { src_a, src_b, dst }
			| Self::LShift { src_a, src_b, dst }
			| Self::RShift { src_a, src_b, dst }
			| Self::Mod { src_a, src_b, dst }
			| Self::And { src_a, src_b, dst }
			| Self::Or { src_a, src_b, dst } => {
				writeln!(f, "    {} {}, {} => {}", self.inst_name(), src_a, src_b, dst)
			}
			Self::ImmAdd { src, konst, dst }
			| Self::ImmSub { src, konst, dst }
			| Self::ImmMult { src, konst, dst }
			| Self::ImmLShift { src, konst, dst }
			| Self::ImmRShift { src, konst, dst } => {
				writeln!(f, "    {} {}, {} => {}", self.inst_name(), src, konst, dst)
			}

			Self::ImmLoad { src, dst } => {
				writeln!(f, "    {} {} => {}", self.inst_name(), src, dst)
			}
			Self::LoadAddImm { src, add, dst } => {
				writeln!(f, "    {} {}, {} => {}", self.inst_name(), src, add, dst)
			}
			Self::LoadAdd { src, add, dst } => {
				writeln!(f, "    {} {}, {} => {}", self.inst_name(), src, add, dst)
			}
			Self::StoreAddImm { src, add, dst } => {
				writeln!(f, "    {} {} => {}, {}", self.inst_name(), src, dst, add)
			}
			Self::StoreAdd { src, add, dst } => {
				writeln!(f, "    {} {} => {}, {}", self.inst_name(), src, dst, add)
			}

			Self::CmpLT { a, b, dst }
			| Self::CmpLE { a, b, dst }
			| Self::CmpGT { a, b, dst }
			| Self::CmpGE { a, b, dst }
			| Self::CmpEQ { a, b, dst }
			| Self::CmpNE { a, b, dst }
			| Self::Comp { a, b, dst }
			// unsigned
			| Self::Compu { a, b, dst }
			| Self::CmpuGE { a, b, dst }
			| Self::CmpuGT { a, b, dst }
			| Self::CmpuLE { a, b, dst }
			| Self::CmpuLT { a, b, dst } => {
				writeln!(f, "    {} {}, {} => {}", self.inst_name(), a, b, dst)
			}

			Self::TestEQ { test, dst }
			| Self::TestNE { test, dst }
			| Self::TestGT { test, dst }
			| Self::TestGE { test, dst }
			| Self::TestLT { test, dst }
			| Self::TestLE { test, dst }
			// Unsigned
			| Self::TestuGT { test, dst }
			| Self::TestuGE { test, dst }
			| Self::TestuLT { test, dst }
			| Self::TestuLE { test, dst } => {
				writeln!(f, "    {} {} => {}", self.inst_name(), test, dst)
			}
			Self::ImmJump(label) => writeln!(f, "    {} -> {}", self.inst_name(), label),
			Self::Jump(reg) => writeln!(f, "    {} -> {}", self.inst_name(), reg),
			Self::Call { name, args } => writeln!(
				f,
				"    {} {}{} {}",
				self.inst_name(),
				name,
				if args.is_empty() { "" } else { "," },
				args.iter().map(|r| r.to_string()).collect::<Vec<_>>().join(", ")
			),
			Self::ImmCall { name, args, ret } => writeln!(
				f,
				"    {} {}, {} => {}",
				self.inst_name(),
				name,
				args.iter().map(|r| r.to_string()).collect::<Vec<_>>().join(", "),
				ret
			),
			Self::ImmRCall { reg, args, ret } => writeln!(
				f,
				"    {} {}, {} => {}",
				self.inst_name(),
				reg,
				args.iter().map(|r| r.to_string()).collect::<Vec<_>>().join(", "),
				ret
			),
			Self::ImmRet(reg) => writeln!(f, "    {} {}", self.inst_name(), reg),
			Self::CbrT { cond, loc } | Self::CbrF { cond, loc } => {
				writeln!(f, "    {} {} -> {}", self.inst_name(), cond, loc)
			}
			Self::CbrLT { a, b, loc }
			| Self::CbrLE { a, b, loc }
			| Self::CbrGT { a, b, loc }
			| Self::CbrGE { a, b, loc }
			| Self::CbrEQ { a, b, loc }
			| Self::CbrNE { a, b, loc }
			// unsigned
			| Self::CbruGE { a, b, loc }
			| Self::CbruGT { a, b, loc }
			| Self::CbruLE { a, b, loc }
			| Self::CbruLT { a, b, loc } => {
				writeln!(f, "    {} {}, {} -> {}", self.inst_name(), a, b, loc)
			}

			Self::RShiftu { src_a, src_b, dst } => {
				writeln!(f, "    {} {}, {} => {}", self.inst_name(), src_a, src_b, dst)
			}
			Self::ImmRShiftu { src, konst, dst } => {
				writeln!(f, "    {} {}, {} => {}", self.inst_name(), src, konst, dst)
			}

			Self::FAdd { src_a, src_b, dst }
			| Self::FSub { src_a, src_b, dst }
			| Self::FMult { src_a, src_b, dst }
			| Self::FDiv { src_a, src_b, dst }
			| Self::FComp { src_a, src_b, dst } => {
				writeln!(f, "    {} {}, {} => {}", self.inst_name(), src_a, src_b, dst)
			}

			Self::FLoadAddImm { src, add, dst } => {
				writeln!(f, "    {} {}, {} => {}", self.inst_name(), src, add, dst)
			}
			Self::FLoadAdd { src, add, dst } => {
				writeln!(f, "    {} {}, {} => {}", self.inst_name(), src, add, dst)
			}
			Self::FRead(reg)
			| Self::IRead(reg)
			| Self::FWrite(reg)
			| Self::IWrite(reg)
			| Self::SWrite(reg)
			| Self::PutChar(reg)
			| Self::Free(reg)
			| Self::PushR(reg) => writeln!(f, "    {} {}", self.inst_name(), reg),

			Self::Malloc { size, dst } => {
				writeln!(f, "    {} {} => {}", self.inst_name(), size, dst)
			}
			Self::Realloc { src, size, dst } => {
				writeln!(f, "    {} {}, {} => {}", self.inst_name(), src, size, dst)
			}

			Self::Push(val) => writeln!(f, "    {} {}", self.inst_name(), val),
			Self::Frame { name, size, params } => {
				writeln!(
					f,
					".{} {}, {}{} {}",
					self.inst_name(),
					name,
					size,
					if params.is_empty() { "" } else { "," },
					params.iter().map(|r| r.to_string()).collect::<Vec<_>>().join(", ")
				)
			}
			Self::Global { name, size, align, content } => {
				let mut global = if content.is_empty() {
					String::new()
				} else if let [single_item] = content.as_slice() {
					format!(":	{}", single_item)
				} else {
					let mut buf = ":\n[".to_string();
					let content_str = content.iter().map(|v| {
						match v {
							Val::Integer(i) => format!(".int {}", i),
							Val::UInteger(u) => format!(".uint {}", u),
							Val::Float(f) => format!(".float {}", f),
							Val::Location(loc) => unreachable!("is this posible {}", loc),
							Val::String(c) => format!(".string {}", c),
							Val::Null => ".zeros 4".to_string(),
						}
					}).collect::<Vec<_>>().join(",");
					buf.push_str(&content_str);
					buf.push(']');
					buf
				};

				write!(f, "	.{} {}, {}, {}{}", self.inst_name(), name, size, align, global)
			}
			Self::Array { name, size, content } => {
				write!(f, "    .{} {}, {}, [", self.inst_name(), name, size)?;
				write!(
					f,
					"{}",
					content.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(", ")
				)?;
				writeln!(f, "]")
			}
			Self::String { name, content } => {
				writeln!(f, "    .{} {}, {}", self.inst_name(), name, content)
			}
			Self::Float { name, content } => {
				writeln!(f, "    .{} {}, {}", self.inst_name(), name, content)
			}
			Self::Label(label) if label == ".E_entry" || label == ".E_exit" => Ok(()),
			Self::Label(label) => {
				writeln!(f, "{}: nop", label)
			}
			Self::Text | Self::Data => writeln!(f, "    .{}", self.inst_name()),
			Self::Skip(s) => writeln!(f, "    # {}", s.trim()),
			Self::Phi(reg, s, sub) => writeln!(
				f,
				"# phi({}_{})({})",
				reg,
				sub.unwrap_or(0),
				s.iter().map(|i| i.to_string()).collect::<Vec<_>>().join(", ")
			),
			_ => writeln!(f, "    {}", self.inst_name()),
		}
	}
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum Operand {
	Register(Reg),
	Value(Val),
}

impl Operand {
	/// Copy the `Operand` to register, panic if this is not a `Reg`.
	pub fn copy_to_register(&self) -> Reg {
		match self {
			Operand::Register(r) => *r,
			_ => panic!("`Operand` is not a register {:?}", self),
		}
	}

	/// Clone the `Operand` to value, panic if this is not a `Val`.
	pub fn clone_to_value(&self) -> Val {
		match self {
			Operand::Value(v) => (*v).clone(),
			_ => panic!("`Operand` is not a register {:?}", self),
		}
	}

	pub fn opt_reg(&self) -> Option<Reg> {
		match self {
			Operand::Register(r) => Some(*r),
			_ => None,
		}
	}
}

impl Instruction {
	pub fn new_phi(reg: Reg) -> Self { Self::Phi(reg, BTreeSet::default(), None) }

	pub fn push_global(&mut self, val: Val) {
		let Self::Global { content, .. } = self else {
			unreachable!("this should only be called for global found: {}", self)
		};
		content.push(val);
	}

	pub fn remove_phis(&mut self) {
		match self {
			Self::FLoad { src, dst }
			| Self::F2I { src, dst }
			| Self::I2F { src, dst }
			| Self::F2F { src, dst }
			| Self::I2I { src, dst }
			| Self::Not { src, dst }
			| Self::Load { src, dst }
			| Self::Store { src, dst } => {
				src.remove_phi();
				dst.remove_phi();
			}
			Self::Add { src_a, src_b, dst }
			| Self::Sub { src_a, src_b, dst }
			| Self::Mult { src_a, src_b, dst }
			| Self::Div { src_a, src_b, dst }
			| Self::LShift { src_a, src_b, dst }
			| Self::RShift { src_a, src_b, dst }
			| Self::Mod { src_a, src_b, dst }
			| Self::And { src_a, src_b, dst }
			| Self::Or { src_a, src_b, dst } => {
				src_a.remove_phi();
				src_b.remove_phi();
				dst.remove_phi();
			}
			Self::ImmAdd { src, dst, .. }
			| Self::ImmSub { src, dst, .. }
			| Self::ImmMult { src, dst, .. }
			| Self::ImmLShift { src, dst, .. }
			| Self::ImmRShift { src, dst, .. } => {
				src.remove_phi();
				dst.remove_phi();
			}

			Self::ImmLoad { dst, .. } => {
				dst.remove_phi();
			}
			Self::LoadAddImm { src, dst, .. } | Self::StoreAddImm { src, dst, .. } => {
				src.remove_phi();
				dst.remove_phi();
			}
			Self::LoadAdd { src, add, dst } | Self::StoreAdd { src, add, dst } => {
				src.remove_phi();
				add.remove_phi();
				dst.remove_phi();
			}

			Self::CmpLT { a, b, dst }
			| Self::CmpLE { a, b, dst }
			| Self::CmpGT { a, b, dst }
			| Self::CmpGE { a, b, dst }
			| Self::CmpEQ { a, b, dst }
			| Self::CmpNE { a, b, dst }
			| Self::Comp { a, b, dst }
			// unsigned
			| Self::CmpuLT { a, b, dst }
			| Self::CmpuLE { a, b, dst }
			| Self::CmpuGT { a, b, dst }
			| Self::CmpuGE { a, b, dst }
			| Self::Compu { a, b, dst } => {
				a.remove_phi();
				b.remove_phi();
				dst.remove_phi();
			}

			Self::TestEQ { test, dst }
			| Self::TestNE { test, dst }
			| Self::TestGT { test, dst }
			| Self::TestGE { test, dst }
			| Self::TestLT { test, dst }
			| Self::TestLE { test, dst }
			// unsigned
			| Self::TestuGT { test, dst }
			| Self::TestuGE { test, dst }
			| Self::TestuLT { test, dst }
			| Self::TestuLE { test, dst } => {
				test.remove_phi();
				dst.remove_phi();
			}
			Self::ImmJump(..) => {}
			Self::Jump(reg) => reg.remove_phi(),
			Self::Call { args, .. } => {
				for arg in args {
					arg.remove_phi();
				}
			}
			Self::ImmCall { args, ret, .. } => {
				ret.remove_phi();
				for arg in args {
					arg.remove_phi();
				}
			}
			Self::ImmRCall { reg, args, ret } => {
				reg.remove_phi();
				ret.remove_phi();
				for arg in args {
					arg.remove_phi();
				}
			}
			Self::ImmRet(reg) => reg.remove_phi(),
			Self::CbrT { cond, .. } | Self::CbrF { cond, .. } => {
				cond.remove_phi();
			}
			Self::CbrLT { a, b, .. }
			| Self::CbrLE { a, b, .. }
			| Self::CbrGT { a, b, .. }
			| Self::CbrGE { a, b, .. }
			| Self::CbrEQ { a, b, .. }
			| Self::CbrNE { a, b, .. }
			// unsigned
			| Self::CbruLT { a, b, .. }
			| Self::CbruLE { a, b, .. }
			| Self::CbruGT { a, b, .. }
			| Self::CbruGE { a, b, .. }=> {
				a.remove_phi();
				b.remove_phi();
			}

			// unsigned
			Self::ImmRShiftu { src, dst, .. } => {
				src.remove_phi();
				dst.remove_phi();
			}
			Self::RShiftu { src_a, src_b, dst } => {
				src_a.remove_phi();
				src_b.remove_phi();
				dst.remove_phi();
			}

			Self::FAdd { src_a, src_b, dst }
			| Self::FSub { src_a, src_b, dst }
			| Self::FMult { src_a, src_b, dst }
			| Self::FDiv { src_a, src_b, dst }
			| Self::FComp { src_a, src_b, dst } => {
				src_a.remove_phi();
				src_b.remove_phi();
				dst.remove_phi();
			}

			Self::FLoadAddImm { src, dst, .. } => {
				src.remove_phi();
				dst.remove_phi();
			}
			Self::FLoadAdd { src, add, dst } => {
				src.remove_phi();
				add.remove_phi();
				dst.remove_phi();
			}
			Self::FRead(reg)
			| Self::IRead(reg)
			| Self::FWrite(reg)
			| Self::IWrite(reg)
			| Self::SWrite(reg)
			| Self::PutChar(reg)
			| Self::Free(reg)
			| Self::Malloc { dst: reg, .. }
			| Self::PushR(reg) => reg.remove_phi(),

			Self::Realloc { src, dst, .. } => {
				src.remove_phi();
				dst.remove_phi();
			}

			Self::Push(..) => {}
			Self::Frame { params, .. } => {
				for arg in params {
					arg.remove_phi();
				}
			}
			Self::Global { .. }
			| Self::Array { .. }
			| Self::String { .. }
			| Self::Float { .. }
			| Self::Label(..)
			| Self::Text
			| Self::Data
			| Self::Skip(..) => {}
			Self::Phi(..) => {
				*self = Self::Skip(format!("{}", self));
			}
			_ => {}
		}
	}
	// TODO: make another enum so this isn't so crappy
	// Have
	// enum Instruction {
	//     NoOperands(Inst),
	//     SingleOperand(Inst()),
	//     TwoOperand(Inst { src, dst }),
	//     ...
	// }
	/// Optional target register for instructions with a destination.
	pub fn target_reg(&self) -> Option<&Reg> {
		match self {
			Self::I2I { dst, .. } => Some(dst),
			Self::F2I { dst, .. } => Some(dst),
			Self::I2F { dst, .. } => Some(dst),
			Self::F2F { dst, .. } => Some(dst),
			Self::Add { dst, .. } => Some(dst),
			Self::Sub { dst, .. } => Some(dst),
			Self::Mult { dst, .. } => Some(dst),
			Self::Div { dst, .. } => Some(dst),
			Self::LShift { dst, .. } => Some(dst),
			Self::RShift { dst, .. } => Some(dst),
			Self::Mod { dst, .. } => Some(dst),
			Self::And { dst, .. } => Some(dst),
			Self::Or { dst, .. } => Some(dst),
			Self::Not { dst, .. } => Some(dst),
			Self::ImmAdd { dst, .. } => Some(dst),
			Self::ImmSub { dst, .. } => Some(dst),
			Self::ImmMult { dst, .. } => Some(dst),
			Self::ImmLShift { dst, .. } => Some(dst),
			Self::ImmRShift { dst, .. } => Some(dst),
			// unsigned
			Self::RShiftu { dst, .. } => Some(dst),
			Self::ImmRShiftu { dst, .. } => Some(dst),

			Self::CmpLT { dst, .. } => Some(dst),
			Self::CmpLE { dst, .. } => Some(dst),
			Self::CmpGT { dst, .. } => Some(dst),
			Self::CmpGE { dst, .. } => Some(dst),
			Self::CmpEQ { dst, .. } => Some(dst),
			Self::CmpNE { dst, .. } => Some(dst),
			Self::Comp { dst, .. } => Some(dst),
			// unsinged
			Self::CmpuLT { dst, .. } => Some(dst),
			Self::CmpuLE { dst, .. } => Some(dst),
			Self::CmpuGT { dst, .. } => Some(dst),
			Self::CmpuGE { dst, .. } => Some(dst),
			Self::Compu { dst, .. } => Some(dst),

			Self::TestEQ { dst, .. } => Some(dst),
			Self::TestNE { dst, .. } => Some(dst),
			Self::TestGT { dst, .. } => Some(dst),
			Self::TestGE { dst, .. } => Some(dst),
			Self::TestLT { dst, .. } => Some(dst),
			Self::TestLE { dst, .. } => Some(dst),
			// unsinged
			Self::TestuLT { dst, .. } => Some(dst),
			Self::TestuLE { dst, .. } => Some(dst),
			Self::TestuGT { dst, .. } => Some(dst),
			Self::TestuGE { dst, .. } => Some(dst),

			// Float stuff
			Self::FAdd { dst, .. } => Some(dst),
			Self::FSub { dst, .. } => Some(dst),
			Self::FMult { dst, .. } => Some(dst),
			Self::FDiv { dst, .. } => Some(dst),
			Self::FComp { dst, .. } => Some(dst),

			// Loads
			Self::ImmLoad { dst, .. }
			| Self::Load { dst, .. }
			| Self::LoadAddImm { dst, .. }
			| Self::LoadAdd { dst, .. }
			| Self::FLoad { dst, .. }
			| Self::FLoadAddImm { dst, .. }
			| Self::FLoadAdd { dst, .. } => Some(dst),
			// Call with return `call arg, arg => ret`
			Self::ImmCall { ret, .. }
			| Self::ImmRCall { ret, .. }
			| Self::Malloc { dst: ret, .. }
			| Self::Realloc { dst: ret, .. } => Some(ret),
			_ => None,
		}
	}
	pub fn target_reg_mut(&mut self) -> Option<&mut Reg> {
		match self {
			// Self::Store { dst, .. } => Some(dst),
			// Self::StoreAddImm { dst, .. } => Some(dst),
			// Self::StoreAdd { dst, .. } => Some(dst),
			// Self::IWrite(dst) => Some(dst),
			// Self::SWrite(dst) => Some(dst),
			// Self::FWrite(dst) => Some(dst),
			// Self::IRead(dst) => Some(dst),
			// Self::FRead(dst) => Some(dst),
			Self::I2I { dst, .. }
			| Self::I2F { dst, .. }
			| Self::Add { dst, .. }
			| Self::Sub { dst, .. }
			| Self::Mult { dst, .. }
			| Self::Div { dst, .. }
			| Self::LShift { dst, .. }
			| Self::RShift { dst, .. }
			| Self::Mod { dst, .. }
			| Self::And { dst, .. }
			| Self::Or { dst, .. }
			| Self::Not { dst, .. }
			| Self::ImmAdd { dst, .. }
			| Self::ImmSub { dst, .. }
			| Self::ImmMult { dst, .. }
			| Self::ImmLShift { dst, .. }
			| Self::ImmRShift { dst, .. }
			// unsigned
			| Self::RShiftu { dst, .. }
			| Self::ImmRShiftu { dst, .. }

			| Self::ImmLoad { dst, .. }
			| Self::Load { dst, .. }
			| Self::LoadAddImm { dst, .. }
			| Self::LoadAdd { dst, .. }
			| Self::CmpLT { dst, .. }
			| Self::CmpLE { dst, .. }
			| Self::CmpGT { dst, .. }
			| Self::CmpGE { dst, .. }
			| Self::CmpEQ { dst, .. }
			| Self::CmpNE { dst, .. }
			| Self::Comp { dst, .. }
			// unsinged
			| Self::CmpuLT { dst, .. }
			| Self::CmpuLE { dst, .. }
			| Self::CmpuGT { dst, .. }
			| Self::CmpuGE { dst, .. }
			| Self::Compu { dst, .. }

			| Self::TestEQ { dst, .. }
			| Self::TestNE { dst, .. }
			| Self::TestGT { dst, .. }
			| Self::TestGE { dst, .. }
			| Self::TestLT { dst, .. }
			| Self::TestLE { dst, .. }
			// unsigned
			| Self::TestuGT { dst, .. }
			| Self::TestuGE { dst, .. }
			| Self::TestuLT { dst, .. }
			| Self::TestuLE { dst, .. }

			| Self::F2I { dst, .. }
			| Self::F2F { dst, .. }
			| Self::FAdd { dst, .. }
			| Self::FSub { dst, .. }
			| Self::FMult { dst, .. }
			| Self::FDiv { dst, .. }
			| Self::FComp { dst, .. }
			| Self::FLoad { dst, .. }
			| Self::FLoadAddImm { dst, .. }
			| Self::FLoadAdd { dst, .. } => Some(dst),
			// Call with return `call arg, arg => ret`
			Self::ImmCall { ret, .. }
			| Self::ImmRCall { ret, .. }
			| Self::Malloc { dst: ret, .. }
			| Self::Realloc { dst: ret, .. } => Some(ret),
			_ => None,
		}
	}

	pub fn operand_iter_mut(&mut self) -> Vec<&mut Reg> {
		match self {
			Self::I2I { src, .. }
			| Self::F2I { src, .. }
			| Self::I2F { src, .. }
			| Self::F2F { src, .. }
			| Self::Not { src, .. }
			| Self::FLoad { src, .. }
			| Self::Load { src, .. } => vec![src],

			Self::Add { src_a, src_b, .. }
			| Self::Sub { src_a, src_b, .. }
			| Self::Mult { src_a, src_b, .. }
			| Self::Div { src_a, src_b, .. }
			| Self::LShift { src_a, src_b, .. }
			| Self::RShift { src_a, src_b, .. }
			// unsigned
			| Self::RShiftu { src_a, src_b, .. }

			| Self::Mod { src_a, src_b, .. }
			| Self::And { src_a, src_b, .. }
			| Self::Or { src_a, src_b, .. }
			| Self::FAdd { src_a, src_b, .. }
			| Self::FSub { src_a, src_b, .. }
			| Self::FMult { src_a, src_b, .. }
			| Self::FDiv { src_a, src_b, .. }
			| Self::FComp { src_a, src_b, .. } => vec![src_a, src_b],

			Self::ImmAdd { src, .. }
			| Self::ImmSub { src, .. }
			| Self::ImmMult { src, .. }
			| Self::ImmLShift { src, .. }
			| Self::ImmRShift { src, .. }
			// unsigned
			| Self::ImmRShiftu { src, .. }

			| Self::LoadAddImm { src, .. }
			| Self::FLoadAddImm { src, .. } => vec![src],

			Self::StoreAddImm { src, dst, .. } => vec![src, dst],
			Self::StoreAdd { src, add, dst } => vec![src, add, dst],
			Self::Store { src, dst } => vec![src, dst],

			// TODO: I think this is correct
			// Self::ImmLoad { src, .. } => vec![],
			Self::LoadAdd { src, add, .. } | Self::FLoadAdd { src, add, .. } => {
				vec![src, add]
			}

			Self::IWrite(r)
			| Self::FWrite(r)
			| Self::SWrite(r)
			| Self::IRead(r)
			| Self::PutChar(r)
			| Self::Free(r)
			| Self::Realloc { src: r, .. }
			| Self::Malloc { size: r, .. }
			| Self::FRead(r) => vec![r],

			Self::CmpLT { a, b, .. }
			| Self::CmpLE { a, b, .. }
			| Self::CmpGT { a, b, .. }
			| Self::CmpGE { a, b, .. }
			| Self::CmpEQ { a, b, .. }
			| Self::CmpNE { a, b, .. }
			| Self::Comp { a, b, .. }
			// unsigned
			| Self::CmpuLT { a, b, .. }
			| Self::CmpuLE { a, b, .. }
			| Self::CmpuGT { a, b, .. }
			| Self::CmpuGE { a, b, .. }
			| Self::Compu { a, b, .. }

			| Self::CbrEQ { a, b, .. }
			| Self::CbrNE { a, b, .. }
			| Self::CbrGT { a, b, .. }
			| Self::CbrGE { a, b, .. }
			| Self::CbrLT { a, b, .. }
			| Self::CbrLE { a, b, .. }
			// unsigned
			| Self::CbrGT { a, b, .. }
			| Self::CbrGE { a, b, .. }
			| Self::CbrLT { a, b, .. }
			| Self::CbrLE { a, b, .. } => vec![a, b],

			Self::CbrT { cond, .. } | Self::CbrF { cond, .. } => vec![cond],

			Self::TestEQ { test, .. }
			| Self::TestNE { test, .. }
			| Self::TestGT { test, .. }
			| Self::TestGE { test, .. }
			| Self::TestLT { test, .. }
			| Self::TestLE { test, .. }
			// unsigned
			| Self::TestuGT { test, .. }
			| Self::TestuGE { test, .. }
			| Self::TestuLT { test, .. }
			| Self::TestuLE { test, .. } => vec![test],

			Self::Call { args, .. } | Self::ImmCall { args, .. } => args.iter_mut().collect(),
			Self::ImmRet(ret) => vec![ret],

			_ => vec![],
		}
	}

	pub fn operand_iter(&self) -> Vec<Reg> {
		match self {
			Self::I2I { src, .. }
			| Self::F2I { src, .. }
			| Self::I2F { src, .. }
			| Self::F2F { src, .. }
			| Self::Not { src, .. }
			| Self::FLoad { src, .. }
			| Self::Load { src, .. } => vec![*src],

			Self::Add { src_a, src_b, .. }
			| Self::Sub { src_a, src_b, .. }
			| Self::Mult { src_a, src_b, .. }
			| Self::Div { src_a, src_b, .. }
			| Self::LShift { src_a, src_b, .. }
			| Self::RShift { src_a, src_b, .. }
			// unsigned
			| Self::RShiftu { src_a, src_b, .. }

			| Self::Mod { src_a, src_b, .. }
			| Self::And { src_a, src_b, .. }
			| Self::Or { src_a, src_b, .. }
			| Self::FAdd { src_a, src_b, .. }
			| Self::FSub { src_a, src_b, .. }
			| Self::FMult { src_a, src_b, .. }
			| Self::FDiv { src_a, src_b, .. }
			| Self::FComp { src_a, src_b, .. } => vec![*src_a, *src_b],

			Self::ImmAdd { src, .. }
			| Self::ImmSub { src, .. }
			| Self::ImmMult { src, .. }
			| Self::ImmLShift { src, .. }
			| Self::ImmRShift { src, .. }
			// unsigned
			| Self::ImmRShiftu { src, .. }

			| Self::LoadAddImm { src, .. }
			| Self::FLoadAddImm { src, .. } => vec![*src],

			Self::StoreAddImm { src, dst, .. } => vec![*src, *dst],
			Self::StoreAdd { src, add, dst } => vec![*src, *add, *dst],
			Self::Store { src, dst } => vec![*src, *dst],

			// TODO: I think this is correct
			// Self::ImmLoad { src, .. } => vec![],
			Self::LoadAdd { src, add, .. } | Self::FLoadAdd { src, add, .. } => {
				vec![*src, *add]
			}

			Self::IWrite(r)
			| Self::FWrite(r)
			| Self::SWrite(r)
			| Self::IRead(r)
			| Self::PutChar(r)
			| Self::Free(r)
			| Self::Realloc { src: r, .. }
			| Self::Malloc { size: r, .. }
			| Self::FRead(r) => vec![*r],

			Self::CmpLT { a, b, .. }
			| Self::CmpLE { a, b, .. }
			| Self::CmpGT { a, b, .. }
			| Self::CmpGE { a, b, .. }
			| Self::CmpEQ { a, b, .. }
			| Self::CmpNE { a, b, .. }
			| Self::Comp { a, b, .. }
			// unsigned
			| Self::CmpuLT { a, b, .. }
			| Self::CmpuLE { a, b, .. }
			| Self::CmpuGT { a, b, .. }
			| Self::CmpuGE { a, b, .. }
			| Self::Compu { a, b, .. }

			| Self::CbrEQ { a, b, .. }
			| Self::CbrNE { a, b, .. }
			| Self::CbrGT { a, b, .. }
			| Self::CbrGE { a, b, .. }
			| Self::CbrLT { a, b, .. }
			| Self::CbrLE { a, b, .. }
			// unsigned
			| Self::CbruGT { a, b, .. }
			| Self::CbruGE { a, b, .. }
			| Self::CbruLT { a, b, .. }
			| Self::CbruLE { a, b, .. } => vec![*a, *b],

			Self::CbrT { cond, .. } | Self::CbrF { cond, .. } => vec![*cond],

			Self::TestEQ { test, .. }
			| Self::TestNE { test, .. }
			| Self::TestGT { test, .. }
			| Self::TestGE { test, .. }
			| Self::TestLT { test, .. }
			| Self::TestLE { test, .. }
			// unsigned
			| Self::TestuGT { test, .. }
			| Self::TestuGE { test, .. }
			| Self::TestuLT { test, .. }
			| Self::TestuLE { test, .. } => vec![*test],

			Self::Call { args, .. } | Self::ImmCall { args, .. } => args.clone(),
			Self::ImmRet(ret) => vec![*ret],

			_ => vec![],
		}
	}

	/// The return value is (left, right) `Option<Operand>`.
	pub fn operands(&self) -> (Option<Operand>, Option<Operand>) {
		match self {
			Self::I2I { src, .. }
			| Self::Not { src, .. }
			| Self::Load { src, .. }
			| Self::F2I { src, .. }
			| Self::I2F { src, .. }
			| Self::F2F { src, .. } => (Some(Operand::Register(*src)), None),

			Self::Add { src_a, src_b, .. }
			| Self::Sub { src_a, src_b, .. }
			| Self::Mult { src_a, src_b, .. }
			| Self::Div { src_a, src_b, .. }
			| Self::LShift { src_a, src_b, .. }
			| Self::RShift { src_a, src_b, .. }
			// unsigned
			| Self::RShiftu { src_a, src_b, .. }

			| Self::Mod { src_a, src_b, .. }
			| Self::And { src_a, src_b, .. }
			| Self::Or { src_a, src_b, .. } => {
				(Some(Operand::Register(*src_a)), Some(Operand::Register(*src_b)))
			}
			Self::ImmAdd { src, konst, .. }
			| Self::ImmSub { src, konst, .. }
			| Self::ImmMult { src, konst, .. }
			| Self::ImmLShift { src, konst, .. }
			| Self::ImmRShift { src, konst, .. }
			// unsigned
			| Self::ImmRShiftu { src, konst, .. } => {
				(Some(Operand::Register(*src)), Some(Operand::Value(konst.clone())))
			}
			Self::ImmLoad { src, .. } => (Some(Operand::Value(src.clone())), None),
			Self::LoadAddImm { src, add, .. } => {
				(Some(Operand::Register(*src)), Some(Operand::Value(add.clone())))
			}
			Self::LoadAdd { src, add, .. } => {
				(Some(Operand::Register(*src)), Some(Operand::Register(*add)))
			}
			Self::Store { src, dst } => {
				(Some(Operand::Register(*src)), Some(Operand::Register(*dst)))
			}
			Self::StoreAddImm { src, add, .. } => {
				(Some(Operand::Register(*src)), Some(Operand::Value(add.clone())))
			}
			Self::StoreAdd { src, add, .. } => {
				(Some(Operand::Register(*src)), Some(Operand::Register(*add)))
			}
			Self::IWrite(r)
			| Self::FWrite(r)
			| Self::SWrite(r)
			| Self::PutChar(r)
			| Self::Free(r)
			| Self::Malloc { size: r, .. }
			| Self::Realloc { src: r, .. } => (Some(Operand::Register(*r)), None),
			Self::IRead(r) | Self::FRead(r) => (Some(Operand::Register(*r)), None),

			Self::CmpLT { a, b, .. }
			| Self::CmpLE { a, b, .. }
			| Self::CmpGT { a, b, .. }
			| Self::CmpGE { a, b, .. }
			| Self::CmpEQ { a, b, .. }
			| Self::CmpNE { a, b, .. }
			| Self::Comp { a, b, .. }
			// unsigned
			| Self::CmpuLT { a, b, .. }
			| Self::CmpuLE { a, b, .. }
			| Self::CmpuGT { a, b, .. }
			| Self::CmpuGE { a, b, .. }
			| Self::Compu { a, b, .. } => (Some(Operand::Register(*a)), Some(Operand::Register(*b))),
			Self::CbrT { cond, .. } | Self::CbrF { cond, .. } => {
				(Some(Operand::Register(*cond)), None)
			}
			Self::CbrEQ { a, b, .. }
			| Self::CbrNE { a, b, .. }
			| Self::CbrGT { a, b, .. }
			| Self::CbrGE { a, b, .. }
			| Self::CbrLT { a, b, .. }
			| Self::CbrLE { a, b, .. }
			// unsigned
			| Self::CbruGT { a, b, .. }
			| Self::CbruGE { a, b, .. }
			| Self::CbruLT { a, b, .. }
			| Self::CbruLE { a, b, .. } => {
				(Some(Operand::Register(*a)), Some(Operand::Register(*b)))
			}
			Self::TestEQ { test, .. }
			| Self::TestNE { test, .. }
			| Self::TestGT { test, .. }
			| Self::TestGE { test, .. }
			| Self::TestLT { test, .. }
			| Self::TestLE { test, .. }
			// unsigned
			| Self::TestuGT { test, .. }
			| Self::TestuGE { test, .. }
			| Self::TestuLT { test, .. }
			| Self::TestuLE { test, .. } => (Some(Operand::Register(*test)), None),

			Self::FAdd { src_a, src_b, .. }
			| Self::FSub { src_a, src_b, .. }
			| Self::FMult { src_a, src_b, .. }
			| Self::FDiv { src_a, src_b, .. }
			| Self::FComp { src_a, src_b, .. } => {
				(Some(Operand::Register(*src_a)), Some(Operand::Register(*src_b)))
			}
			Self::FLoad { src, .. } => (Some(Operand::Register(*src)), None),
			Self::FLoadAddImm { src, add, .. } => {
				(Some(Operand::Register(*src)), Some(Operand::Value(add.clone())))
			}
			Self::FLoadAdd { src, add, .. } => {
				(Some(Operand::Register(*src)), Some(Operand::Register(*add)))
			}
			Self::ImmRet(ret) => (Some(Operand::Register(*ret)), None),

			_ => (None, None),
		}
	}

	/// The return value is (left, right) `Option<&mut Reg>`.
	pub fn operands_mut(&mut self) -> (Option<&mut Reg>, Option<&mut Reg>) {
		match self {
			Self::I2I { src, .. }
			| Self::Not { src, .. }
			| Self::F2I { src, .. }
			| Self::I2F { src, .. }
			| Self::F2F { src, .. } => (Some(src), None),
			Self::Add { src_a, src_b, .. }
			| Self::Sub { src_a, src_b, .. }
			| Self::Mult { src_a, src_b, .. }
			| Self::Div { src_a, src_b, .. }
			| Self::LShift { src_a, src_b, .. }
			| Self::RShift { src_a, src_b, .. }
			// unsigned
			| Self::RShiftu { src_a, src_b, .. }

			| Self::Mod { src_a, src_b, .. }
			| Self::And { src_a, src_b, .. }
			| Self::Or { src_a, src_b, .. } => (Some(src_a), Some(src_b)),
			Self::ImmAdd { src, .. }
			| Self::ImmSub { src, .. }
			| Self::ImmMult { src, .. }
			| Self::ImmLShift { src, .. }
			| Self::ImmRShift { src, .. }
			// unsigned
			| Self::ImmRShiftu { src, .. }

			| Self::Load { src, .. }
			| Self::LoadAddImm { src, .. }
			| Self::Store { src, .. }
			| Self::StoreAddImm { src, .. } => (Some(src), None),
			Self::LoadAdd { src, add, .. } | Self::StoreAdd { src, add, .. } => {
				(Some(src), Some(add))
			}
			Self::IWrite(r)
			| Self::SWrite(r)
			| Self::FWrite(r)
			| Self::IRead(r)
			| Self::PutChar(r)
			| Self::Free(r)
			| Self::Realloc { src: r, .. }
			| Self::Malloc { size: r, .. }
			| Self::FRead(r) => (Some(r), None),

			Self::CmpLT { a, b, .. }
			| Self::CmpLE { a, b, .. }
			| Self::CmpGT { a, b, .. }
			| Self::CmpGE { a, b, .. }
			| Self::CmpEQ { a, b, .. }
			| Self::CmpNE { a, b, .. }
			| Self::Comp { a, b, .. }
			// unsigned
			| Self::CmpuLT { a, b, .. }
			| Self::CmpuLE { a, b, .. }
			| Self::CmpuGT { a, b, .. }
			| Self::CmpuGE { a, b, .. }
			| Self::Compu { a, b, .. } => (Some(a), Some(b)),

			Self::CbrLT { a, b, .. }
			| Self::CbrLE { a, b, .. }
			| Self::CbrGT { a, b, .. }
			| Self::CbrGE { a, b, .. }
			| Self::CbrEQ { a, b, .. }
			| Self::CbrNE { a, b, .. }
			// unsigned
			| Self::CbruGT { a, b, .. }
			| Self::CbruGE { a, b, .. }
			| Self::CbruLT { a, b, .. }
			| Self::CbruLE { a, b, .. } => (Some(a), Some(b)),

			Self::CbrT { cond, .. } | Self::CbrF { cond, .. } => (Some(cond), None),

			Self::TestEQ { test, .. }
			| Self::TestNE { test, .. }
			| Self::TestGT { test, .. }
			| Self::TestGE { test, .. }
			| Self::TestLT { test, .. }
			| Self::TestLE { test, .. }
			// unsigned
			| Self::TestuGT { test, .. }
			| Self::TestuGE { test, .. }
			| Self::TestuLT { test, .. }
			| Self::TestuLE { test, .. } => (Some(test), None),

			Self::FAdd { src_a, src_b, .. }
			| Self::FSub { src_a, src_b, .. }
			| Self::FMult { src_a, src_b, .. }
			| Self::FDiv { src_a, src_b, .. }
			| Self::FComp { src_a, src_b, .. } => (Some(src_a), Some(src_b)),
			Self::FLoad { src, .. } => (Some(src), None),
			Self::FLoadAddImm { src, add: _, .. } => (Some(src), None),
			Self::FLoadAdd { src, add, .. } => (Some(src), Some(add)),
			Self::ImmRet(ret) => (Some(ret), None),
			_ => (None, None),
		}
	}

	pub const fn inst_name(&self) -> &'static str {
		match self {
			Self::I2I { .. } => "i2i",
			Self::Add { .. } => "add",
			Self::Sub { .. } => "sub",
			Self::Mult { .. } => "mult",
			Self::Div { .. } => "div",
			Self::LShift { .. } => "lshift",
			Self::RShift { .. } => "rshift",
			// unsigned
			Self::RShiftu { .. } => "rshiftu",
			Self::Mod { .. } => "mod",
			Self::And { .. } => "and",
			Self::Or { .. } => "or",
			Self::Not { .. } => "not",
			Self::ImmAdd { .. } => "addI",
			Self::ImmSub { .. } => "subI",
			Self::ImmMult { .. } => "multI",
			Self::ImmLShift { .. } => "lshiftI",
			Self::ImmRShift { .. } => "rshiftI",
			// unsigned
			Self::ImmRShiftu { .. } => "rshiftuI",
			Self::ImmLoad { .. } => "loadI",
			Self::Load { .. } => "load",
			Self::LoadAddImm { .. } => "loadAI",
			Self::LoadAdd { .. } => "loadAO",
			Self::Store { .. } => "store",
			Self::StoreAddImm { .. } => "storeAI",
			Self::StoreAdd { .. } => "storeAO",
			Self::CmpLT { .. } => "cmp_LT",
			Self::CmpLE { .. } => "cmp_LE",
			Self::CmpGT { .. } => "cmp_GT",
			Self::CmpGE { .. } => "cmp_GE",
			Self::CmpEQ { .. } => "cmp_EQ",
			Self::CmpNE { .. } => "cmp_NE",
			Self::Comp { .. } => "comp",
			// unsigned
			Self::CmpuLT { .. } => "cmpu_LT",
			Self::CmpuLE { .. } => "cmpu_LE",
			Self::CmpuGT { .. } => "cmpu_GT",
			Self::CmpuGE { .. } => "cmpu_GE",
			Self::Compu { .. } => "compu",

			Self::TestEQ { .. } => "testeq",
			Self::TestNE { .. } => "testne",
			Self::TestGT { .. } => "testgt",
			Self::TestGE { .. } => "testge",
			Self::TestLT { .. } => "testlt",
			Self::TestLE { .. } => "testle",
			// unsigned
			Self::TestuGT { .. } => "testugt",
			Self::TestuGE { .. } => "testuge",
			Self::TestuLT { .. } => "testult",
			Self::TestuLE { .. } => "testule",

			Self::ImmJump(_) => "jumpI",
			Self::Jump(_) => "jump",
			Self::Call { .. } => "call",
			Self::ImmCall { .. } => "icall",
			Self::ImmRCall { .. } => "ircall",
			Self::Ret => "ret",
			Self::ImmRet(_) => "iret",
			Self::CbrT { .. } => "cbr",
			Self::CbrF { .. } => "cbrne",
			Self::CbrLT { .. } => "cbr_LT",
			Self::CbrLE { .. } => "cbr_LE",
			Self::CbrGT { .. } => "cbr_GT",
			Self::CbrGE { .. } => "cbr_GE",
			Self::CbrEQ { .. } => "cbr_EQ",
			Self::CbrNE { .. } => "cbr_NE",
			// unsigned
			Self::CbruLT { .. } => "cbru_LT",
			Self::CbruLE { .. } => "cbru_LE",
			Self::CbruGT { .. } => "cbru_GT",
			Self::CbruGE { .. } => "cbru_GE",

			Self::F2I { .. } => "f2i",
			Self::I2F { .. } => "i2f",
			Self::F2F { .. } => "f2f",
			Self::FAdd { .. } => "fadd",
			Self::FSub { .. } => "fsub",
			Self::FMult { .. } => "fmult",
			Self::FDiv { .. } => "fdiv",
			Self::FComp { .. } => "fcomp",
			Self::FLoad { .. } => "fload",
			Self::FLoadAddImm { .. } => "floadAI",
			Self::FLoadAdd { .. } => "floadAO",
			Self::FRead(_) => "fread",
			Self::IRead(_) => "iread",
			Self::FWrite(_) => "fwrite",
			Self::IWrite(_) => "iwrite",
			Self::SWrite(_) => "swrite",
			Self::PutChar(_) => "putchar",
			Self::Free(_) => "free",
			Self::Malloc { .. } => "malloc",
			Self::Realloc { .. } => "realloc",
			Self::Push(_) => "push",
			Self::PushR(_) => "pushr",
			Self::Pop => "pop",
			Self::Data => "data",
			Self::Text => "text",
			Self::Frame { .. } => "frame",
			Self::Global { .. } => "global",
			Self::Array { .. } => "array",
			Self::String { .. } => "string",
			Self::Float { .. } => "float",
			Self::Label(_) => "label",
			Self::Skip(..) | Self::Phi(..) => {
				panic!("should never print a skip or phi instruction")
			}
		}
	}

	/// Any `jumpI` or conditional branch instructions.
	pub fn uses_label(&self) -> Option<&str> {
		match self {
			Self::ImmJump(loc)
			| Self::CbrT { loc, .. }
			| Self::CbrF { loc, .. }
			| Self::CbrLT { loc, .. }
			| Self::CbrLE { loc, .. }
			| Self::CbrGT { loc, .. }
			| Self::CbrGE { loc, .. }
			| Self::CbrEQ { loc, .. }
			| Self::CbrNE { loc, .. }
			// unsinged
			| Self::CbruLT { loc, .. }
			| Self::CbruLE { loc, .. }
			| Self::CbruGT { loc, .. }
			| Self::CbruGE { loc, .. } => Some(&loc.0),
			_ => None,
		}
	}

	pub fn label_mut(&mut self) -> Option<&mut Loc> {
		match self {
			Self::ImmJump(loc)
			| Self::CbrT { loc, .. }
			| Self::CbrF { loc, .. }
			| Self::CbrLT { loc, .. }
			| Self::CbrLE { loc, .. }
			| Self::CbrGT { loc, .. }
			| Self::CbrGE { loc, .. }
			| Self::CbrEQ { loc, .. }
			| Self::CbrNE { loc, .. }
			// unsinged
			| Self::CbruLT { loc, .. }
			| Self::CbruLE { loc, .. }
			| Self::CbruGT { loc, .. }
			| Self::CbruGE { loc, .. } => Some(loc),
			_ => None,
		}
	}

	pub fn is_cnd_jump(&self) -> bool {
		matches!(
			self,
			Self::CbrT { .. }
				| Self::CbrF { .. }
				| Self::CbrLT { .. }
				| Self::CbrLE { .. }
				| Self::CbrGT { .. }
				| Self::CbrGE { .. }
				| Self::CbrEQ { .. }
				| Self::CbrNE { .. }
				// unsinged
				| Self::CbruLT { .. }
				| Self::CbruLE { .. }
				| Self::CbruGT { .. }
				| Self::CbruGE { .. }
		)
	}

	pub fn unconditional_jmp(&self) -> bool { matches!(self, Self::ImmJump(..)) }

	pub fn is_return(&self) -> bool { matches!(self, Self::Ret | Self::ImmRet(_)) }

	/// Turn any instruction that would be more efficient as a move. This will not move
	/// around existing `i2i` and `f2f` instructions since there is no gain.
	pub fn as_new_move_instruction(&self, src: Reg, dst: Reg) -> Option<Self> {
		match self {
			Self::Add { .. }
			| Self::Sub { .. }
			| Self::Mult { .. }
			| Self::LShift { .. }
			| Self::RShift { .. }
			| Self::RShiftu { .. }
			| Self::Mod { .. }
			| Self::And { .. }
			| Self::Or { .. }
			| Self::Not { .. }
			| Self::ImmAdd { .. }
			| Self::ImmSub { .. }
			| Self::ImmMult { .. }
			| Self::ImmLShift { .. }
			| Self::ImmRShift { .. }
			| Self::ImmRShiftu { .. }
			| Self::ImmLoad { .. }
			| Self::Load { .. }
			| Self::LoadAddImm { .. }
			| Self::LoadAdd { .. } => Some(Self::I2I { src, dst }),
			Self::I2F { .. }
			| Self::F2F { .. }
			| Self::FAdd { .. }
			| Self::FSub { .. }
			| Self::FMult { .. }
			| Self::FDiv { .. }
			| Self::FComp { .. }
			| Self::FLoad { .. }
			| Self::FLoadAddImm { .. }
			| Self::FLoadAdd { .. } => Some(Self::F2F { src, dst }),
			Self::Store { .. } | Self::StoreAddImm { .. } | Self::IRead(_) | Self::FRead(_) => {
				unreachable!("cannot simplify store instruction")
			}
			Self::I2I { .. } | Self::F2F { .. } => None,
			_ => unreachable!(
				"stack, text/data section stuff, calls, jumps, and comp/test stuff {:?}",
				self
			),
		}
	}

	pub fn fold(&self, a: &Val, b: &Val) -> Option<Self> {
		Some(match (a, b) {
			(Val::Integer(a), Val::Integer(b)) => match self {
				Self::Add { dst, .. } => Self::ImmLoad { src: Val::Integer(a + b), dst: *dst },
				Self::Sub { dst, .. } => Self::ImmLoad { src: Val::Integer(a - b), dst: *dst },
				Self::Mult { dst, .. } => Self::ImmLoad { src: Val::Integer(a * b), dst: *dst },
				Self::LShift { dst, .. } => Self::ImmLoad { src: Val::Integer(a << b), dst: *dst },
				Self::RShift { dst, .. } => Self::ImmLoad { src: Val::Integer(a >> b), dst: *dst },
				Self::RShiftu { dst, .. } => Self::ImmLoad { src: Val::Integer(a >> b), dst: *dst },
				Self::Mod { dst, .. } if *b != 0 => {
					Self::ImmLoad { src: Val::Integer(a % b), dst: *dst }
				}
				Self::And { dst, .. } => Self::ImmLoad { src: Val::Integer(a & b), dst: *dst },
				Self::Or { dst, .. } => Self::ImmLoad { src: Val::Integer(a | b), dst: *dst },
				_ => {
					return None;
				}
			},
			(Val::Float(_), Val::Float(_)) => match self {
				Self::F2F { dst: _, .. }
				| Self::FAdd { dst: _, .. }
				| Self::FSub { dst: _, .. }
				| Self::FMult { dst: _, .. }
				| Self::FDiv { dst: _, .. }
				| Self::FComp { dst: _, .. } => todo!(),
				_ => {
					return None;
				}
			},
			_ => {
				return None;
			}
		})
	}

	pub fn fold_two_address(&self, a: Val) -> Option<Self> {
		Some(match self {
			Self::Load { dst, .. } => Self::ImmLoad { src: a, dst: *dst },
			_ => {
				return None;
			}
		})
	}

	/// If this operation is an identity operation, return the register that would be
	/// unchanged.
	///
	/// `add %vr2, 0 => %vr3` is the same as `i2i %vr2 => %vr3`
	///
	/// TODO:
	/// 2 * a = a + a, a / 1 = a, a / a = 1 if a != 0,
	/// a >> 0 = a, a << 0 = a, a && a = a, a || a = a
	pub fn identity_register(&self) -> Option<Reg> {
		Some(match self {
			Self::Add { .. } | Self::FAdd { .. } => match self.operands() {
				// TODO: can they be swapped or just `op %vr2, 10 => %vr3`
				(Some(Operand::Value(val)), Some(Operand::Register(reg)))
				| (Some(Operand::Register(reg)), Some(Operand::Value(val)))
					if val.is_zero() =>
				{
					reg
				}
				_ => {
					return None;
				}
			},
			Self::Sub { .. } | Self::FSub { .. } => match self.operands() {
				(Some(Operand::Register(reg)), Some(Operand::Value(val))) if val.is_zero() => reg,
				(Some(Operand::Register(a)), Some(Operand::Register(b))) if a == b => {
					todo!("this is sub id 0")
				}
				_ => {
					return None;
				}
			},
			Self::Mult { .. } | Self::FMult { .. } => match self.operands() {
				(Some(Operand::Value(val)), Some(Operand::Register(reg)))
				| (Some(Operand::Register(reg)), Some(Operand::Value(val)))
					if val.is_one() =>
				{
					reg
				}
				_ => {
					return None;
				}
			},
			Self::FDiv { .. } => match self.operands() {
				(Some(Operand::Register(reg)), Some(Operand::Value(val))) if val.is_one() => reg,
				(Some(Operand::Register(a)), Some(Operand::Register(b))) if a == b => {
					todo!("this is div id 1")
				}
				_ => {
					return None;
				}
			},
			Self::LShift { .. } | Self::RShift { .. } => match self.operands() {
				(Some(Operand::Value(val)), Some(Operand::Register(reg)))
				| (Some(Operand::Register(reg)), Some(Operand::Value(val)))
					if val.is_zero() =>
				{
					reg
				}
				_ => {
					return None;
				}
			},
			// TODO: hmm is this right
			Self::Mod { .. } => match self.operands() {
				(Some(Operand::Value(val)), Some(Operand::Register(reg)))
				| (Some(Operand::Register(reg)), Some(Operand::Value(val)))
					if val.is_one() =>
				{
					reg
				}
				_ => {
					return None;
				}
			},
			Self::And { .. } => match self.operands() {
				(Some(Operand::Register(a)), Some(Operand::Register(b))) if a == b => a,
				_ => {
					return None;
				}
			},
			Self::Or { dst: _, .. } => match self.operands() {
				(Some(Operand::Register(a)), Some(Operand::Register(b))) if a == b => a,
				_ => {
					return None;
				}
			},
			_ => {
				return None;
			}
		})
	}

	/// If this operation is an identity operation, return the register that would be
	/// unchanged. `val` is always the left operand, subtraction is __never__ a valid
	/// identity op for this call.
	///
	/// `add %vr2, 0 => %vr3` is the same as `i2i %vr2 => %vr3`
	pub fn identity_with_const_prop_left(&self, val: &Val) -> Option<&Reg> {
		Some(match self {
			Self::Add { src_b, .. } | Self::FAdd { src_b, .. } if val.is_zero() => src_b,
			Self::Mult { src_b, .. } | Self::FMult { src_b, .. } if val.is_one() => src_b,
			Self::And { .. } => todo!(),
			Self::Or { dst: _, .. } => todo!(),
			_ => {
				return None;
			}
		})
	}

	/// If this operation is an identity operation, return the register that would be
	/// unchanged. `val` is always the right operand, subtraction is a valid identity
	/// op.
	///
	/// `add %vr2, 0 => %vr3` is the same as `i2i %vr2 => %vr3`
	pub fn identity_with_const_prop_right(&self, val: &Val) -> Option<&Reg> {
		Some(match self {
			Self::Add { src_a, .. } | Self::FAdd { src_a, .. } if val.is_zero() => src_a,
			Self::Sub { src_a, .. } | Self::FSub { src_a, .. } if val.is_zero() => src_a,
			Self::Mult { src_a, .. } | Self::FMult { src_a, .. } if val.is_one() => src_a,
			Self::FDiv { src_a, .. } if val.is_one() => src_a,
			Self::Mod { src_a, .. } if val.is_one() => src_a,
			Self::LShift { src_a, .. } if val.is_zero() => src_a,
			Self::RShift { src_a, .. } if val.is_zero() => src_a,
			Self::And { .. } => todo!(),
			Self::Or { dst: _, .. } => todo!(),
			_ => {
				return None;
			}
		})
	}

	pub fn as_immediate_instruction_right(&self, a: &Val) -> Option<Self> {
		Some(match self {
			Self::Add { src_a, dst, .. } => {
				Self::ImmAdd { src: *src_a, konst: a.clone(), dst: *dst }
			}
			Self::Sub { src_a, dst, .. } => {
				Self::ImmSub { src: *src_a, konst: a.clone(), dst: *dst }
			}
			Self::Mult { src_a, dst, .. } => {
				Self::ImmMult { src: *src_a, konst: a.clone(), dst: *dst }
			}
			Self::LShift { src_a, dst, .. } => {
				Self::ImmLShift { src: *src_a, konst: a.clone(), dst: *dst }
			}
			Self::RShift { src_a, dst, .. } => {
				Self::ImmRShift { src: *src_a, konst: a.clone(), dst: *dst }
			}
			Self::F2F { dst: _, .. }
			| Self::FAdd { dst: _, .. }
			| Self::FSub { dst: _, .. }
			| Self::FMult { dst: _, .. }
			| Self::FDiv { dst: _, .. }
			| Self::FComp { dst: _, .. } => todo!(),
			_ => {
				return None;
			}
		})
	}

	pub fn as_immediate_instruction_left(&self, a: &Val) -> Option<Self> {
		Some(match self {
			Self::Add { src_b, dst, .. } => {
				Self::ImmAdd { src: *src_b, konst: a.clone(), dst: *dst }
			}
			Self::Mult { src_b, dst, .. } => {
				Self::ImmMult { src: *src_b, konst: a.clone(), dst: *dst }
			}
			Self::ImmAdd { konst, dst, .. } => Self::ImmLoad { src: a.add(konst)?, dst: *dst },
			Self::ImmMult { konst, dst, .. } => Self::ImmLoad { src: a.mult(konst)?, dst: *dst },
			Self::RShift { src_a, dst, .. } => {
				Self::ImmRShift { src: *src_a, konst: a.clone(), dst: *dst }
			}
			Self::F2F { dst: _, .. }
			| Self::FAdd { dst: _, .. }
			| Self::FSub { dst: _, .. }
			| Self::FMult { dst: _, .. }
			| Self::FDiv { dst: _, .. }
			| Self::FComp { dst: _, .. } => todo!(),
			_ => {
				return None;
			}
		})
	}

	/// If the instruction is any `store` or any `read`.
	pub fn is_store(&self) -> bool {
		matches!(
			self,
			Self::Store { .. } | Self::StoreAddImm { .. } | Self::IRead(_) | Self::FRead(_)
		)
	}

	/// If the instruction is any `load`.
	pub fn is_load(&self) -> bool {
		matches!(
			self,
			Self::Load { .. }
				| Self::LoadAddImm { .. }
				| Self::LoadAdd { .. }
				| Self::ImmLoad { .. }
		)
	}

	pub fn is_call_instruction(&self) -> bool {
		matches!(
			self,
			Self::Call { .. }
				| Self::ImmCall { .. }
				| Self::ImmRCall { .. }
				| Self::Malloc { .. }
				| Self::Free(..) | Self::Realloc { .. }
		)
	}

	pub fn is_load_imm(&self) -> bool {
		matches!(self, Self::ImmLoad { src: Val::Integer(..) | Val::Float(..), .. })
	}

	pub fn is_commutative(&self) -> bool {
		matches!(
			self,
			Self::Add { .. } | Self::ImmAdd { .. } | Self::Mult { .. } | Self::ImmMult { .. }
		)
	}

	pub fn is_phi(&self) -> bool { matches!(self, Self::Phi(..)) }

	pub fn is_tmp_expr(&self) -> bool {
		matches!(
			self,
			Self::Add { .. }
				| Self::Sub { .. }
				| Self::Mult { .. }
				| Self::LShift { .. }
				| Self::RShift { .. }
				| Self::RShiftu { .. }
				| Self::Mod { .. }
				| Self::And { .. }
				| Self::Or { .. }
				| Self::Not { .. }
				| Self::ImmAdd { .. }
				| Self::ImmSub { .. }
				| Self::ImmMult { .. }
				| Self::ImmLShift { .. }
				| Self::ImmRShift { .. }
				| Self::ImmRShiftu { .. }
				| Self::FAdd { .. }
				| Self::FSub { .. }
				| Self::FMult { .. }
				| Self::ImmLoad { src: Val::Integer(..) | Val::Float(..), .. }
		)
	}

	pub(crate) fn registers_mut_iter(&mut self) -> Vec<&mut Reg> {
		match self {
			Self::I2I { src, dst }
			| Self::F2I { src, dst }
			| Self::I2F { src, dst }
			| Self::F2F { src, dst }
			| Self::Not { src, dst }
			| Self::FLoad { src, dst }
			| Self::Load { src, dst } => vec![src, dst],

			Self::Add { src_a, src_b, dst }
			| Self::Sub { src_a, src_b, dst }
			| Self::Mult { src_a, src_b, dst }
			| Self::Div { src_a, src_b, dst }
			| Self::LShift { src_a, src_b, dst }
			| Self::RShift { src_a, src_b, dst }
			| Self::RShiftu { src_a, src_b, dst }
			| Self::Mod { src_a, src_b, dst }
			| Self::And { src_a, src_b, dst }
			| Self::Or { src_a, src_b, dst }
			| Self::FAdd { src_a, src_b, dst }
			| Self::FSub { src_a, src_b, dst }
			| Self::FMult { src_a, src_b, dst }
			| Self::FDiv { src_a, src_b, dst }
			| Self::FComp { src_a, src_b, dst } => vec![src_a, src_b, dst],

			Self::ImmAdd { src, dst, .. }
			| Self::ImmSub { src, dst, .. }
			| Self::ImmMult { src, dst, .. }
			| Self::ImmLShift { src, dst, .. }
			| Self::ImmRShift { src, dst, .. }
			| Self::ImmRShiftu { src, dst, .. }
			| Self::LoadAddImm { src, dst, .. }
			| Self::FLoadAddImm { src, dst, .. } => vec![src, dst],

			Self::StoreAddImm { src, dst, .. } => vec![src, dst],
			Self::StoreAdd { src, add, dst } => vec![src, add, dst],

			// TODO: I think this is correct
			// Self::ImmLoad { src, .. } => vec![],
			Self::LoadAdd { src, add, dst } | Self::FLoadAdd { src, add, dst } => {
				vec![src, add, dst]
			}

			Self::Store { src, dst } | Self::Load { src, dst } => vec![src, dst],

			Self::IWrite(r)
			| Self::FWrite(r)
			| Self::SWrite(r)
			| Self::IRead(r)
			| Self::PutChar(r)
			| Self::FRead(r)
			| Self::Free(r) => vec![r],

			Self::Malloc { dst, .. } => vec![dst],
			Self::Realloc { src, dst, .. } => vec![src, dst],

			Self::CmpLT { a, b, dst }
			| Self::CmpLE { a, b, dst }
			| Self::CmpGT { a, b, dst }
			| Self::CmpGE { a, b, dst }
			| Self::CmpEQ { a, b, dst }
			| Self::CmpNE { a, b, dst }
			| Self::Comp { a, b, dst }
			// unsigned
			| Self::CmpLT { a, b, dst }
			| Self::CmpLE { a, b, dst }
			| Self::CmpGT { a, b, dst }
			| Self::CmpGE { a, b, dst }
			| Self::Compu { a, b, dst } => vec![a, b, dst],

			Self::CbrEQ { a, b, .. }
			| Self::CbrNE { a, b, .. }
			| Self::CbrGT { a, b, .. }
			| Self::CbrGE { a, b, .. }
			| Self::CbrLT { a, b, .. }
			| Self::CbrLE { a, b, .. }
			// unsigned
			| Self::CbruLT { a, b, .. }
			| Self::CbruLE { a, b, .. }
			| Self::CbruGT { a, b, .. }
			| Self::CbruGE { a, b, .. } => vec![a, b],

			Self::CbrT { cond, .. } | Self::CbrF { cond, .. } => vec![cond],

			Self::TestEQ { test, dst }
			| Self::TestNE { test, dst }
			| Self::TestGT { test, dst }
			| Self::TestGE { test, dst }
			| Self::TestLT { test, dst }
			| Self::TestLE { test, dst }
			// unsigned
			| Self::TestuGT { test, dst }
			| Self::TestuGE { test, dst }
			| Self::TestuLT { test, dst }
			| Self::TestuLE { test, dst } => vec![test, dst],

			Self::Call { args, .. } | Self::Frame { params: args, .. } => args.iter_mut().collect(),
			Self::ImmCall { args, ret, .. } => args.iter_mut().chain(Some(ret)).collect(),
			Self::ImmRet(ret) => vec![ret],

			Self::ImmLoad { dst, .. } => vec![dst],

			_ => vec![],
		}
	}

	pub(crate) fn registers_iter(&self) -> Vec<&Reg> {
		match self {
			Self::I2I { src, dst }
			| Self::F2I { src, dst }
			| Self::I2F { src, dst }
			| Self::F2F { src, dst }
			| Self::Not { src, dst }
			| Self::FLoad { src, dst }
			| Self::Load { src, dst } => vec![src, dst],

			Self::Add { src_a, src_b, dst }
			| Self::Sub { src_a, src_b, dst }
			| Self::Mult { src_a, src_b, dst }
			| Self::LShift { src_a, src_b, dst }
			| Self::RShift { src_a, src_b, dst }
			// unsigned
			| Self::RShiftu { src_a, src_b, dst }
			| Self::Mod { src_a, src_b, dst }
			| Self::And { src_a, src_b, dst }
			| Self::Or { src_a, src_b, dst }
			| Self::FAdd { src_a, src_b, dst }
			| Self::FSub { src_a, src_b, dst }
			| Self::FMult { src_a, src_b, dst }
			| Self::FDiv { src_a, src_b, dst }
			| Self::FComp { src_a, src_b, dst } => vec![src_a, src_b, dst],

			Self::ImmAdd { src, dst, .. }
			| Self::ImmSub { src, dst, .. }
			| Self::ImmMult { src, dst, .. }
			| Self::ImmLShift { src, dst, .. }
			| Self::ImmRShift { src, dst, .. }
			// unsigned
			| Self::ImmRShiftu { src, dst, .. }
			| Self::LoadAddImm { src, dst, .. }
			| Self::FLoadAddImm { src, dst, .. } => vec![src, dst],

			Self::StoreAddImm { src, dst, .. } => vec![src, dst],
			Self::StoreAdd { src, add, dst } => vec![src, add, dst],

			Self::LoadAdd { src, add, dst } | Self::FLoadAdd { src, add, dst } => {
				vec![src, add, dst]
			}

			Self::Store { src, dst } | Self::Load { src, dst } => vec![src, dst],

			Self::IWrite(r)
			| Self::FWrite(r)
			| Self::SWrite(r)
			| Self::IRead(r)
			| Self::PutChar(r)
			| Self::FRead(r)
			| Self::Free(r) => vec![r],

			Self::Malloc { dst, .. } => vec![dst],
			Self::Realloc { src, dst, .. } => vec![src, dst],

			Self::CmpLT { a, b, dst }
			| Self::CmpLE { a, b, dst }
			| Self::CmpGT { a, b, dst }
			| Self::CmpGE { a, b, dst }
			| Self::CmpEQ { a, b, dst }
			| Self::CmpNE { a, b, dst }
			| Self::Comp { a, b, dst }
			// unsigned
			| Self::CmpuLT { a, b, dst }
			| Self::CmpuLE { a, b, dst }
			| Self::CmpuGT { a, b, dst }
			| Self::CmpuGE { a, b, dst }
			| Self::Compu { a, b, dst } => vec![a, b, dst],

			Self::CbrEQ { a, b, .. }
			| Self::CbrNE { a, b, .. }
			| Self::CbrGT { a, b, .. }
			| Self::CbrGE { a, b, .. }
			| Self::CbrLT { a, b, .. }
			| Self::CbrLE { a, b, .. }
			// unsinged
			| Self::CbruGT { a, b, .. }
			| Self::CbruGE { a, b, .. }
			| Self::CbruLT { a, b, .. }
			| Self::CbruLE { a, b, .. } => vec![a, b],

			Self::CbrT { cond, .. } | Self::CbrF { cond, .. } => vec![cond],

			Self::TestEQ { test, dst }
			| Self::TestNE { test, dst }
			| Self::TestGT { test, dst }
			| Self::TestGE { test, dst }
			| Self::TestLT { test, dst }
			| Self::TestLE { test, dst }
			// unsigned
			| Self::TestuGT { test, dst }
			| Self::TestuGE { test, dst }
			| Self::TestuLT { test, dst }
			| Self::TestuLE { test, dst } => vec![test, dst],

			Self::Call { args, .. } | Self::Frame { params: args, .. } => args.iter().collect(),
			Self::ImmCall { args, ret, .. } => args.iter().chain(Some(ret)).collect(),
			Self::ImmRet(ret) => vec![ret],

			Self::ImmLoad { dst, .. } => vec![dst],

			Self::Label(..) | Self::ImmJump(..) | Self::Ret => vec![],

			what => todo!("{:?}", what),
		}
	}
}

pub fn parse_text(input: &str) -> Result<Vec<Instruction>, &'static str> {
	let mut instructions = vec![];

	let mut in_global_seq = None;
	for line in input.lines() {
		let comp = line.split_whitespace().map(|s| s.replace(',', "")).collect::<Vec<_>>();
		if comp.is_empty() {
			continue;
		}

		match comp.iter().map(|s| s.as_str()).collect::<Vec<_>>().as_slice() {
			// Integer operations
			["i2i", src, "=>", dst] => instructions
				.push(Instruction::I2I { src: Reg::from_str(src)?, dst: Reg::from_str(dst)? }),
			["add", a, b, "=>", dst] => instructions.push(Instruction::Add {
				src_a: Reg::from_str(a)?,
				src_b: Reg::from_str(b)?,
				dst: Reg::from_str(dst)?,
			}),
			["sub", a, b, "=>", dst] => instructions.push(Instruction::Sub {
				src_a: Reg::from_str(a)?,
				src_b: Reg::from_str(b)?,
				dst: Reg::from_str(dst)?,
			}),
			["mult", a, b, "=>", dst] => instructions.push(Instruction::Mult {
				src_a: Reg::from_str(a)?,
				src_b: Reg::from_str(b)?,
				dst: Reg::from_str(dst)?,
			}),
			["lshift", a, b, "=>", dst] => instructions.push(Instruction::LShift {
				src_a: Reg::from_str(a)?,
				src_b: Reg::from_str(b)?,
				dst: Reg::from_str(dst)?,
			}),
			["rshift", a, b, "=>", dst] => instructions.push(Instruction::RShift {
				src_a: Reg::from_str(a)?,
				src_b: Reg::from_str(b)?,
				dst: Reg::from_str(dst)?,
			}),
			["rshiftu", a, b, "=>", dst] => instructions.push(Instruction::RShiftu {
				src_a: Reg::from_str(a)?,
				src_b: Reg::from_str(b)?,
				dst: Reg::from_str(dst)?,
			}),
			["div", a, b, "=>", dst] => instructions.push(Instruction::Div {
				src_a: Reg::from_str(a)?,
				src_b: Reg::from_str(b)?,
				dst: Reg::from_str(dst)?,
			}),
			["mod", a, b, "=>", dst] => instructions.push(Instruction::Mod {
				src_a: Reg::from_str(a)?,
				src_b: Reg::from_str(b)?,
				dst: Reg::from_str(dst)?,
			}),
			["and", a, b, "=>", dst] => instructions.push(Instruction::And {
				src_a: Reg::from_str(a)?,
				src_b: Reg::from_str(b)?,
				dst: Reg::from_str(dst)?,
			}),
			["or", a, b, "=>", dst] => instructions.push(Instruction::Or {
				src_a: Reg::from_str(a)?,
				src_b: Reg::from_str(b)?,
				dst: Reg::from_str(dst)?,
			}),
			["not", src, "=>", dst] => instructions
				.push(Instruction::Not { src: Reg::from_str(src)?, dst: Reg::from_str(dst)? }),
			["addI", a, b, "=>", dst] => instructions.push(Instruction::ImmAdd {
				src: Reg::from_str(a)?,
				konst: Val::from_str(b)?,
				dst: Reg::from_str(dst)?,
			}),
			["subI", a, b, "=>", dst] => instructions.push(Instruction::ImmSub {
				src: Reg::from_str(a)?,
				konst: Val::from_str(b)?,
				dst: Reg::from_str(dst)?,
			}),
			["multI", a, b, "=>", dst] => instructions.push(Instruction::ImmMult {
				src: Reg::from_str(a)?,
				konst: Val::from_str(b)?,
				dst: Reg::from_str(dst)?,
			}),
			["lshiftI", a, b, "=>", dst] => instructions.push(Instruction::ImmLShift {
				src: Reg::from_str(a)?,
				konst: Val::from_str(b)?,
				dst: Reg::from_str(dst)?,
			}),
			["rshiftI", a, b, "=>", dst] => instructions.push(Instruction::ImmRShift {
				src: Reg::from_str(a)?,
				konst: Val::from_str(b)?,
				dst: Reg::from_str(dst)?,
			}),
			["rshiftuI", a, b, "=>", dst] => instructions.push(Instruction::ImmRShiftu {
				src: Reg::from_str(a)?,
				konst: Val::UInteger(b.parse().map_err(|_| "failed to parse uint")?),
				dst: Reg::from_str(dst)?,
			}),

			// Memory operations
			["loadI", src, "=>", dst] => {
				instructions.push(Instruction::ImmLoad {
					src: Val::from_str(src)?,
					dst: Reg::from_str(dst)?,
				});
			}
			["load", src, "=>", dst] => instructions
				.push(Instruction::Load { src: Reg::from_str(src)?, dst: Reg::from_str(dst)? }),
			["loadAI", a, b, "=>", dst] => instructions.push(Instruction::LoadAddImm {
				src: Reg::from_str(a)?,
				add: Val::from_str(b)?,
				dst: Reg::from_str(dst)?,
			}),
			["loadAO", a, b, "=>", dst] => instructions.push(Instruction::LoadAdd {
				src: Reg::from_str(a)?,
				add: Reg::from_str(b)?,
				dst: Reg::from_str(dst)?,
			}),
			["store", src, "=>", dst] => instructions
				.push(Instruction::Store { src: Reg::from_str(src)?, dst: Reg::from_str(dst)? }),
			["storeAI", a, "=>", b, konst] => instructions.push(Instruction::StoreAddImm {
				src: Reg::from_str(a)?,
				add: Val::from_str(konst)?,
				dst: Reg::from_str(b)?,
			}),
			["storeAO", a, "=>", b, add] => instructions.push(Instruction::StoreAdd {
				src: Reg::from_str(a)?,
				add: Reg::from_str(add)?,
				dst: Reg::from_str(b)?,
			}),
			// Compare operations
			["cmp_LT", a, b, "=>", dst] => instructions.push(Instruction::CmpLT {
				a: Reg::from_str(a)?,
				b: Reg::from_str(b)?,
				dst: Reg::from_str(dst)?,
			}),
			["cmp_LE", a, b, "=>", dst] => instructions.push(Instruction::CmpLE {
				a: Reg::from_str(a)?,
				b: Reg::from_str(b)?,
				dst: Reg::from_str(dst)?,
			}),
			["cmp_GT", a, b, "=>", dst] => instructions.push(Instruction::CmpGT {
				a: Reg::from_str(a)?,
				b: Reg::from_str(b)?,
				dst: Reg::from_str(dst)?,
			}),
			["cmp_GE", a, b, "=>", dst] => instructions.push(Instruction::CmpGE {
				a: Reg::from_str(a)?,
				b: Reg::from_str(b)?,
				dst: Reg::from_str(dst)?,
			}),
			["cmp_EQ", a, b, "=>", dst] => instructions.push(Instruction::CmpEQ {
				a: Reg::from_str(a)?,
				b: Reg::from_str(b)?,
				dst: Reg::from_str(dst)?,
			}),
			["cmp_NE", a, b, "=>", dst] => instructions.push(Instruction::CmpNE {
				a: Reg::from_str(a)?,
				b: Reg::from_str(b)?,
				dst: Reg::from_str(dst)?,
			}),
			["comp", a, b, "=>", dst] => instructions.push(Instruction::Comp {
				a: Reg::from_str(a)?,
				b: Reg::from_str(b)?,
				dst: Reg::from_str(dst)?,
			}),
			// unsigned
			["cmpu_LT", a, b, "=>", dst] => instructions.push(Instruction::CmpuLT {
				a: Reg::from_str(a)?,
				b: Reg::from_str(b)?,
				dst: Reg::from_str(dst)?,
			}),
			["cmpu_LE", a, b, "=>", dst] => instructions.push(Instruction::CmpuLE {
				a: Reg::from_str(a)?,
				b: Reg::from_str(b)?,
				dst: Reg::from_str(dst)?,
			}),
			["cmpu_GT", a, b, "=>", dst] => instructions.push(Instruction::CmpuGT {
				a: Reg::from_str(a)?,
				b: Reg::from_str(b)?,
				dst: Reg::from_str(dst)?,
			}),
			["cmpu_GE", a, b, "=>", dst] => instructions.push(Instruction::CmpuGE {
				a: Reg::from_str(a)?,
				b: Reg::from_str(b)?,
				dst: Reg::from_str(dst)?,
			}),
			["compu", a, b, "=>", dst] => instructions.push(Instruction::Compu {
				a: Reg::from_str(a)?,
				b: Reg::from_str(b)?,
				dst: Reg::from_str(dst)?,
			}),
			["testeq", a, "=>", dst] => instructions
				.push(Instruction::TestEQ { test: Reg::from_str(a)?, dst: Reg::from_str(dst)? }),
			["testne", a, "=>", dst] => instructions
				.push(Instruction::TestNE { test: Reg::from_str(a)?, dst: Reg::from_str(dst)? }),
			["testgt", a, "=>", dst] => instructions
				.push(Instruction::TestGT { test: Reg::from_str(a)?, dst: Reg::from_str(dst)? }),
			["testge", a, "=>", dst] => instructions
				.push(Instruction::TestGE { test: Reg::from_str(a)?, dst: Reg::from_str(dst)? }),
			["testlt", a, "=>", dst] => instructions
				.push(Instruction::TestLT { test: Reg::from_str(a)?, dst: Reg::from_str(dst)? }),
			["testle", a, "=>", dst] => instructions
				.push(Instruction::TestLE { test: Reg::from_str(a)?, dst: Reg::from_str(dst)? }),
			// unsigned
			["testugt", a, "=>", dst] => instructions
				.push(Instruction::TestuGT { test: Reg::from_str(a)?, dst: Reg::from_str(dst)? }),
			["testuge", a, "=>", dst] => instructions
				.push(Instruction::TestuGE { test: Reg::from_str(a)?, dst: Reg::from_str(dst)? }),
			["testult", a, "=>", dst] => instructions
				.push(Instruction::TestuLT { test: Reg::from_str(a)?, dst: Reg::from_str(dst)? }),
			["testule", a, "=>", dst] => instructions
				.push(Instruction::TestuLE { test: Reg::from_str(a)?, dst: Reg::from_str(dst)? }),

			// Float operations
			["f2i", src, "=>", dst] => instructions
				.push(Instruction::F2I { src: Reg::from_str(src)?, dst: Reg::from_str(dst)? }),
			["i2f", src, "=>", dst] => instructions
				.push(Instruction::I2F { src: Reg::from_str(src)?, dst: Reg::from_str(dst)? }),
			["f2f", src, "=>", dst] => instructions
				.push(Instruction::F2F { src: Reg::from_str(src)?, dst: Reg::from_str(dst)? }),
			["fadd", a, b, "=>", dst] => instructions.push(Instruction::FAdd {
				src_a: Reg::from_str(a)?,
				src_b: Reg::from_str(b)?,
				dst: Reg::from_str(dst)?,
			}),
			["fsub", a, b, "=>", dst] => instructions.push(Instruction::FSub {
				src_a: Reg::from_str(a)?,
				src_b: Reg::from_str(b)?,
				dst: Reg::from_str(dst)?,
			}),
			["fmult", a, b, "=>", dst] => instructions.push(Instruction::FMult {
				src_a: Reg::from_str(a)?,
				src_b: Reg::from_str(b)?,
				dst: Reg::from_str(dst)?,
			}),
			["fdiv", a, b, "=>", dst] => instructions.push(Instruction::FDiv {
				src_a: Reg::from_str(a)?,
				src_b: Reg::from_str(b)?,
				dst: Reg::from_str(dst)?,
			}),
			["fcomp", a, b, "=>", dst] => instructions.push(Instruction::FComp {
				src_a: Reg::from_str(a)?,
				src_b: Reg::from_str(b)?,
				dst: Reg::from_str(dst)?,
			}),
			["fload", a, "=>", dst] => instructions
				.push(Instruction::FLoad { src: Reg::from_str(a)?, dst: Reg::from_str(dst)? }),
			["floadAI", a, b, "=>", dst] => instructions.push(Instruction::FLoadAddImm {
				src: Reg::from_str(a)?,
				add: Val::from_str(b)?,
				dst: Reg::from_str(dst)?,
			}),
			["floadAO", a, b, "=>", dst] => instructions.push(Instruction::FLoadAdd {
				src: Reg::from_str(a)?,
				add: Reg::from_str(b)?,
				dst: Reg::from_str(dst)?,
			}),

			// I/O operations
			["fread", target] => instructions.push(Instruction::FRead(Reg::from_str(target)?)),
			["iread", target] => instructions.push(Instruction::IRead(Reg::from_str(target)?)),
			["fwrite", src] => instructions.push(Instruction::FWrite(Reg::from_str(src)?)),
			["iwrite", src] => instructions.push(Instruction::IWrite(Reg::from_str(src)?)),
			["swrite", src] => instructions.push(Instruction::SWrite(Reg::from_str(src)?)),
			["putchar", src] => instructions.push(Instruction::PutChar(Reg::from_str(src)?)),

			["free", src] => instructions.push(Instruction::Free(Reg::from_str(src)?)),
			["malloc", size, "=>", dst] => instructions
				.push(Instruction::Malloc { size: Reg::from_str(size)?, dst: Reg::from_str(dst)? }),
			["realloc", src, size, "=>", dst] => instructions.push(Instruction::Realloc {
				src: Reg::from_str(src)?,
				size: Reg::from_str(size)?,
				dst: Reg::from_str(dst)?,
			}),

			// Branch operations
			["jumpI", "->", label] => {
				instructions.push(Instruction::ImmJump(Loc::from_str(label)?))
			}
			["jump", "->", target] => instructions.push(Instruction::Jump(Reg::from_str(target)?)),
			["call", name, args @ ..] => {
				let args = args
					.iter()
					.map(|s| Reg::from_str(s))
					.collect::<Result<Vec<_>, &'static str>>()?;
				instructions.push(Instruction::Call { name: name.to_string(), args })
			}
			["icall", name, args @ .., "=>", ret] => {
				let args = args
					.iter()
					.map(|s| Reg::from_str(s))
					.collect::<Result<Vec<_>, &'static str>>()?;

				instructions.push(Instruction::ImmCall {
					name: name.to_string(),
					args,
					ret: Reg::from_str(ret)?,
				})
			}
			["ircall", reg, args @ .., "=>", ret] => {
				let args = args
					.iter()
					.map(|s| Reg::from_str(s))
					.collect::<Result<Vec<_>, &'static str>>()?;
				instructions.push(Instruction::ImmRCall {
					reg: Reg::from_str(reg)?,
					args,
					ret: Reg::from_str(ret)?,
				})
			}
			["ret"] => instructions.push(Instruction::Ret),
			["iret", res] => instructions.push(Instruction::ImmRet(Reg::from_str(res)?)),
			["cbr", src, "->", label] => instructions
				.push(Instruction::CbrT { cond: Reg::from_str(src)?, loc: Loc::from_str(label)? }),
			["cbrne", src, "->", label] => instructions
				.push(Instruction::CbrF { cond: Reg::from_str(src)?, loc: Loc::from_str(label)? }),
			["cbr_LT", a, b, "->", label] => instructions.push(Instruction::CbrLT {
				a: Reg::from_str(a)?,
				b: Reg::from_str(b)?,
				loc: Loc::from_str(label)?,
			}),
			["cbr_LE", a, b, "->", label] => instructions.push(Instruction::CbrLE {
				a: Reg::from_str(a)?,
				b: Reg::from_str(b)?,
				loc: Loc::from_str(label)?,
			}),
			["cbr_GT", a, b, "->", label] => instructions.push(Instruction::CbrGT {
				a: Reg::from_str(a)?,
				b: Reg::from_str(b)?,
				loc: Loc::from_str(label)?,
			}),
			["cbr_GE", a, b, "->", label] => instructions.push(Instruction::CbrGE {
				a: Reg::from_str(a)?,
				b: Reg::from_str(b)?,
				loc: Loc::from_str(label)?,
			}),
			["cbr_EQ", a, b, "->", label] => instructions.push(Instruction::CbrEQ {
				a: Reg::from_str(a)?,
				b: Reg::from_str(b)?,
				loc: Loc::from_str(label)?,
			}),
			["cbr_NE", a, b, "->", label] => instructions.push(Instruction::CbrNE {
				a: Reg::from_str(a)?,
				b: Reg::from_str(b)?,
				loc: Loc::from_str(label)?,
			}),
			// unsigned
			["cbru_LT", a, b, "->", label] => instructions.push(Instruction::CbrLE {
				a: Reg::from_str(a)?,
				b: Reg::from_str(b)?,
				loc: Loc::from_str(label)?,
			}),
			["cbru_LE", a, b, "->", label] => instructions.push(Instruction::CbrLE {
				a: Reg::from_str(a)?,
				b: Reg::from_str(b)?,
				loc: Loc::from_str(label)?,
			}),
			["cbru_GT", a, b, "->", label] => instructions.push(Instruction::CbrGT {
				a: Reg::from_str(a)?,
				b: Reg::from_str(b)?,
				loc: Loc::from_str(label)?,
			}),
			["cbru_GE", a, b, "->", label] => instructions.push(Instruction::CbrGE {
				a: Reg::from_str(a)?,
				b: Reg::from_str(b)?,
				loc: Loc::from_str(label)?,
			}),

			// Stack operations
			["push", c] => instructions.push(Instruction::Push(Val::from_str(c)?)),
			["pushr", reg] => instructions.push(Instruction::PushR(Reg::from_str(reg)?)),
			["pop"] => instructions.push(Instruction::Pop),
			// ["stadd"] => instructions.push(Instruction::StAdd),
			// ["stsub"] => instructions.push(Instruction::StSub),
			// ["stmul"] => instructions.push(Instruction::StMul),
			// ["stdiv"] => instructions.push(Instruction::StDiv),
			// ["stlshift"] => instructions.push(Instruction::StLShift),
			// ["strshift"] => instructions.push(Instruction::StRShift),

			// Pseudo operations
			[".data"] => instructions.push(Instruction::Data),
			[".text"] => instructions.push(Instruction::Text),
			[".frame", name, size, params @ ..] => {
				let params = params
					.iter()
					.map(|s| Reg::from_str(s))
					.collect::<Result<Vec<_>, &'static str>>()?;
				instructions.push(Instruction::Frame {
					name: name.to_string(),
					size: size.parse().map_err(|_| "failed to parse .frame size")?,
					params,
				})
			}
			[".global", name, size, align] if align.ends_with(':') => {
				let align = align.trim_end_matches(':');

				in_global_seq = Some(Instruction::Global {
					name: name.to_string(),
					size: size.parse().map_err(|_| "failed to parse .global size")?,
					align: align.parse().map_err(|_| "failed to parse .global align")?,
					content: vec![],
				});
			}
			[".global", name, size, align, number] if align.ends_with(':') => {
				let align = align.trim_end_matches(':');

				instructions.push(Instruction::Global {
					name: name.to_string(),
					size: size.parse().map_err(|_| "failed to parse .global size")?,
					align: align.parse().map_err(|_| "failed to parse .global align")?,
					content: vec![Val::from_str(number)?],
				});
			},
			[".global", name, size, align] => instructions.push(Instruction::Global {
				name: name.to_string(),
				size: size.parse().map_err(|_| "failed to parse .global size")?,
				align: align.parse().map_err(|_| "failed to parse .global align")?,
				content: vec![],
			}),
			["[", ty, val] if let Some(curr_global) = &mut in_global_seq => {
				curr_global.push_global(Val::from_str(val)?);
			}
			[ty, val] if let Some(curr_global) = &mut in_global_seq => {
				curr_global.push_global(Val::from_str(val)?);
			}
			[ty, val, "]"] if in_global_seq.is_some() => {
				let mut curr_global = in_global_seq.take().unwrap();
				curr_global.push_global(Val::from_str(val)?);

				instructions.push(curr_global);
			}
			[".string", name, str_lit @ ..] => {
				let text = str_lit.join(" ");
				instructions.push(Instruction::String { name: name.to_string(), content: text });
			}
			[".float", name, val] => instructions.push(Instruction::Float {
				name: name.to_string(),
				content: val.parse().map_err(|_| "failed to parse .float value")?,
			}),
			[label, "nop"] => instructions.push(Instruction::Label(label.replace(':', ""))),
			[first, ..] if first.starts_with('#') => {}
			[label] if label.starts_with('.') => {
				instructions.push(Instruction::Label(label.replace(':', "")))
			}
			inst => todo!("{:?}", inst),
			// _ => {
			//     return Err("invalid instruction sequence");
			// }
		}
	}
	Ok(instructions)
}

#[derive(Debug, Clone)]
pub struct Block {
	pub label: String,
	pub instructions: Vec<Instruction>,
}

impl Block {
	pub fn enter() -> Self {
		Self {
			label: ".E_entry".to_string(),
			instructions: vec![Instruction::Label(".E_entry".to_string())],
		}
	}
	pub fn exit() -> Self {
		Self {
			label: ".E_exit".to_string(),
			instructions: vec![Instruction::Label(".E_exit".to_string())],
		}
	}

	/// All `Instruction`s with `Instruction::Skip` filtered out.
	pub fn instructions(&self) -> impl Iterator<Item = &Instruction> + '_ {
		self.instructions.iter().filter(|i| !matches!(i, Instruction::Skip(..)))
	}

	/// Returns the optional name of the block the conditional branch jumps to, the caller
	/// must find the fall through block name.
	pub fn ends_with_cond_branch(&self) -> Option<&str> {
		self.instructions.last().and_then(|i| i.is_cnd_jump().then(|| i.uses_label()).flatten())
	}
	/// Returns the name of the block if `Instruction` is jump immediate.
	pub fn ends_with_jump(&self) -> Option<&str> {
		match self.instructions.last() {
			Some(Instruction::ImmJump(l)) => Some(l.as_str()),
			_ => None,
		}
	}
}

#[derive(Clone, Debug)]
pub struct Function {
	pub label: String,
	pub stack_size: usize,
	pub params: Vec<Reg>,
	pub blocks: Vec<Block>,
}

impl Function {
	pub fn flatten_block_iter(&self) -> impl Iterator<Item = &Instruction> + '_ {
		struct Iter<'a> {
			iter: &'a [Block],
			blk_idx: usize,
			inst_idx: usize,
		}
		impl<'a> Iterator for Iter<'a> {
			type Item = &'a Instruction;
			fn next(&mut self) -> Option<Self::Item> {
				let blk = self.iter.get(self.blk_idx)?;
				match blk.instructions.get(self.inst_idx) {
					Some(inst) => {
						self.inst_idx += 1;
						Some(inst)
					}
					None => {
						self.blk_idx += 1;
						self.inst_idx = 1; // We use this the next iteration

						self.iter.get(self.blk_idx)?.instructions.get(0)
					}
				}
			}
		}
		Iter { iter: &self.blocks, blk_idx: 0, inst_idx: 0 }
	}
}

#[derive(Debug)]
pub struct IlocProgram {
	/// The .text and .data segments of an iloc program.
	pub preamble: Vec<Instruction>,
	/// Basic blocks.
	pub functions: Vec<Function>,
}

impl IlocProgram {
	pub fn instruction_iter(&self) -> impl Iterator<Item = &Instruction> {
		self.preamble.iter().chain(self.functions.iter().flat_map(|f| f.flatten_block_iter()))
	}
}

pub fn make_blks(iloc: Vec<Instruction>) -> IlocProgram {
	let fn_start =
		iloc.iter().position(|inst| matches!(inst, Instruction::Frame { .. })).unwrap_or_default();
	let (preamble, rest) = iloc.split_at(fn_start);

	let mut functions = vec![];
	let mut fn_idx = 0;
	let mut blk_idx = 0;
	for inst in rest.iter() {
		if let Instruction::Frame { name, size, params } = inst {
			let label = format!(".F_{}", name);
			functions.push(Function {
				label: name.to_string(),
				stack_size: *size,
				params: params.clone(),
				blocks: vec![Block {
					label: label.clone(),
					instructions: vec![inst.clone(), Instruction::Label(label.clone())],
				}],
			});

			fn_idx = functions.len().saturating_sub(1);
			blk_idx = 0;
		} else if let Instruction::Label(label) = inst {
			functions[fn_idx].blocks.push(Block {
				label: label.to_string(),
				instructions: vec![Instruction::Label(label.to_string())],
			});

			blk_idx = functions[fn_idx].blocks.len().saturating_sub(1);
		} else {
			let x = &mut functions[fn_idx];
			x.blocks[blk_idx].instructions.push(inst.clone());
		}
	}

	IlocProgram { preamble: preamble.to_vec(), functions }
}

pub fn make_basic_blocks(iloc: &IlocProgram) -> IlocProgram {
	let mut functions = vec![];
	for func in &iloc.functions {
		let mut blocks = vec![];
		// let mut block_map = HashMap::new();
		// let mut blk_idx = 0;
		for blk in &func.blocks {
			blocks.push(Block { label: blk.label.clone(), instructions: vec![] });
			for (idx, inst) in blk.instructions.iter().enumerate() {
				// We always add the instruction even when it's a cbr/jmp with no block
				// after
				blocks.last_mut().unwrap().instructions.push(inst.clone());

				if inst.is_cnd_jump() && !matches!(blk.instructions.get(idx + 1), None) {
					let label = format!(".{}{}", blocks.len(), blk.label);

					blocks.push(Block {
						label: label.clone(),
						instructions: vec![Instruction::Label(label.clone())],
					});
				}
			}
		}

		functions.push(Function {
			label: func.label.to_string(),
			stack_size: func.stack_size,
			params: func.params.clone(),
			blocks,
		});
	}
	IlocProgram { preamble: iloc.preamble.clone(), functions }
}

#[test]
fn parse_iloc() {
	use std::fs;

	let text = fs::read_to_string("./input/check.il").unwrap();
	parse_text(&text).unwrap();
}
