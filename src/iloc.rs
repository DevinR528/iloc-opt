use std::{
    cmp::Ordering,
    collections::{BTreeSet, HashSet},
    fmt,
    hash::{self, Hash},
    mem::discriminant,
    str::FromStr,
    usize,
};

#[derive(Clone, Debug)]
pub enum Val {
    Integer(isize),
    Float(f64),
    Location(String),
    String(String),
    Null,
}

impl Val {
    pub fn to_int(&self) -> Option<isize> {
        if let Self::Integer(int) = self {
            return Some(*int);
        }
        None
    }
    pub fn to_float(&self) -> Option<f64> {
        if let Self::Float(fl) = self {
            return Some(*fl);
        }
        None
    }

    pub fn add(&self, other: &Self) -> Option<Self> {
        Some(Self::Integer(self.to_int()? + other.to_int()?))
    }

    pub fn sub(&self, other: &Self) -> Option<Self> {
        Some(Self::Integer(self.to_int()? - other.to_int()?))
    }

    pub fn mult(&self, other: &Self) -> Option<Self> {
        Some(Self::Integer(self.to_int()? * other.to_int()?))
    }

    pub fn lshift(&self, other: &Self) -> Option<Self> {
        Some(Self::Integer(self.to_int()? << other.to_int()?))
    }

    pub fn rshift(&self, other: &Self) -> Option<Self> {
        Some(Self::Integer(self.to_int()? >> other.to_int()?))
    }

    pub fn modulus(&self, other: &Self) -> Option<Self> {
        Some(Self::Integer(self.to_int()? % other.to_int()?))
    }

    pub fn and(&self, other: &Self) -> Option<Self> {
        Some(Self::Integer(self.to_int()? & other.to_int()?))
    }

    pub fn or(&self, other: &Self) -> Option<Self> {
        Some(Self::Integer(self.to_int()? | other.to_int()?))
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

    pub fn is_zero(&self) -> bool {
        match self {
            Self::Integer(0) => true,
            Self::Float(num) => *num == 0.0,
            _ => false,
        }
    }
    pub fn is_one(&self) -> bool {
        match self {
            Self::Integer(1) => true,
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
            (Self::Float(a), Self::Float(b)) => Self::Float(if a == b { 1.0 } else { 0.0 }),
            _ => {
                return None;
            }
        })
    }
    pub fn cmp_ne(&self, other: &Self) -> Option<Self> {
        Some(match (self, other) {
            (Self::Integer(a), Self::Integer(b)) => Self::Integer(if a != b { 1 } else { 0 }),
            (Self::Float(a), Self::Float(b)) => Self::Float(if a != b { 1.0 } else { 0.0 }),
            _ => {
                return None;
            }
        })
    }
    pub fn cmp_lt(&self, other: &Self) -> Option<Self> {
        Some(match (self, other) {
            (Self::Integer(a), Self::Integer(b)) => Self::Integer(if a < b { 1 } else { 0 }),
            (Self::Float(a), Self::Float(b)) => Self::Float(if a < b { 1.0 } else { 0.0 }),
            _ => {
                return None;
            }
        })
    }
    pub fn cmp_le(&self, other: &Self) -> Option<Self> {
        Some(match (self, other) {
            (Self::Integer(a), Self::Integer(b)) => Self::Integer(if a <= b { 1 } else { 0 }),
            (Self::Float(a), Self::Float(b)) => Self::Float(if a <= b { 1.0 } else { 0.0 }),
            _ => {
                return None;
            }
        })
    }
    pub fn cmp_gt(&self, other: &Self) -> Option<Self> {
        Some(match (self, other) {
            (Self::Integer(a), Self::Integer(b)) => Self::Integer(if a > b { 1 } else { 0 }),
            (Self::Float(a), Self::Float(b)) => Self::Float(if a > b { 1.0 } else { 0.0 }),
            _ => {
                return None;
            }
        })
    }
    pub fn cmp_ge(&self, other: &Self) -> Option<Self> {
        Some(match (self, other) {
            (Self::Integer(a), Self::Integer(b)) => Self::Integer(if a >= b { 1 } else { 0 }),
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
            Val::Integer(s.parse::<isize>().map_err(|_| {
                println!("{}", s);
                "`Val` parse error"
            })?)
        } else {
            Val::Location(s.to_string())
        })
    }
}
impl fmt::Display for Val {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Val::Integer(int) => int.fmt(f),
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
            Reg::Phi(num, subs) if unsafe { crate::SSA } => write!(f, "%vr{}_{}", num, subs),
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

    /// Convert Phi registers to normal virtual registers.
    pub fn as_register(&self) -> Reg {
        if let Reg::Phi(reg, ..) = self {
            Reg::Var(*reg)
        } else {
            *self
        }
    }

    pub fn as_usize(&self) -> usize {
        if let Reg::Var(curr) = self {
            *curr
        } else {
            unreachable!("not just Reg::Var in hurr")
        }
    }

    pub fn remove_phi(&mut self) {
        if let Reg::Phi(reg, ..) = self {
            *self = Reg::Var(*reg)
        }
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Loc(pub String);

impl Loc {
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}
impl FromStr for Loc {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self(s.to_string()))
    }
}
impl fmt::Display for Loc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
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
    LoadAddImm { src: Reg, add: Val, dst: Reg },
    /// (%r + %r) => %r `loadAO`
    LoadAdd { src: Reg, add: Reg, dst: Reg },
    /// %r => %r `store`
    Store { src: Reg, dst: Reg },
    /// %r => (%r + c) `storeAI`
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
    Global { name: String, size: usize, align: usize },
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
            | Instruction::Comp { a, b, dst } => (a, b, dst, variant).hash(state),
            Instruction::TestEQ { test, dst }
            | Instruction::TestNE { test, dst }
            | Instruction::TestGT { test, dst }
            | Instruction::TestGE { test, dst }
            | Instruction::TestLT { test, dst }
            | Instruction::TestLE { test, dst } => (test, dst, variant).hash(state),
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
            | Instruction::CbrNE { a, b, loc } => (a, b, loc, variant).hash(state),

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
            | Instruction::SWrite(s) => (s, variant).hash(state),
            Instruction::Push(s) => (s, variant).hash(state),
            Instruction::PushR(s) => (s, variant).hash(state),
            Instruction::Frame { name, size, params } => (name, size, params, variant).hash(state),
            Instruction::Global { name, size, align } => (name, size, align, variant).hash(state),
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
            (Self::Push(l0), Self::Push(r0)) => l0 == r0,
            (Self::PushR(l0), Self::PushR(r0)) => l0 == r0,
            (
                Self::Frame { name: l_name, size: l_size, params: l_params },
                Self::Frame { name: r_name, size: r_size, params: r_params },
            ) => l_name == r_name && l_size == r_size && l_params == r_params,
            (
                Self::Global { name: l_name, size: l_size, align: l_align },
                Self::Global { name: r_name, size: r_size, align: r_align },
            ) => l_name == r_name && l_size == r_size && l_align == r_align,
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
            Instruction::FLoad { src, dst }
            | Instruction::F2I { src, dst }
            | Instruction::I2F { src, dst }
            | Instruction::F2F { src, dst }
            | Instruction::I2I { src, dst }
            | Instruction::Not { src, dst }
            | Instruction::Load { src, dst }
            | Instruction::Store { src, dst } => {
                writeln!(f, "    {} {} => {}", self.inst_name(), src, dst)
            }
            Instruction::Add { src_a, src_b, dst }
            | Instruction::Sub { src_a, src_b, dst }
            | Instruction::Mult { src_a, src_b, dst }
            | Instruction::Div { src_a, src_b, dst }
            | Instruction::LShift { src_a, src_b, dst }
            | Instruction::RShift { src_a, src_b, dst }
            | Instruction::Mod { src_a, src_b, dst }
            | Instruction::And { src_a, src_b, dst }
            | Instruction::Or { src_a, src_b, dst } => {
                writeln!(f, "    {} {}, {} => {}", self.inst_name(), src_a, src_b, dst)
            }
            Instruction::ImmAdd { src, konst, dst }
            | Instruction::ImmSub { src, konst, dst }
            | Instruction::ImmMult { src, konst, dst }
            | Instruction::ImmLShift { src, konst, dst }
            | Instruction::ImmRShift { src, konst, dst } => {
                writeln!(f, "    {} {}, {} => {}", self.inst_name(), src, konst, dst)
            }

            Instruction::ImmLoad { src, dst } => {
                writeln!(f, "    {} {} => {}", self.inst_name(), src, dst)
            }
            Instruction::LoadAddImm { src, add, dst }
            | Instruction::StoreAddImm { src, add, dst } => {
                writeln!(f, "    {} {}, {} => {}", self.inst_name(), src, add, dst)
            }
            Instruction::LoadAdd { src, add, dst } | Instruction::StoreAdd { src, add, dst } => {
                writeln!(f, "    {} {}, {} => {}", self.inst_name(), src, add, dst)
            }

            Instruction::CmpLT { a, b, dst }
            | Instruction::CmpLE { a, b, dst }
            | Instruction::CmpGT { a, b, dst }
            | Instruction::CmpGE { a, b, dst }
            | Instruction::CmpEQ { a, b, dst }
            | Instruction::CmpNE { a, b, dst }
            | Instruction::Comp { a, b, dst } => {
                writeln!(f, "    {} {}, {} => {}", self.inst_name(), a, b, dst)
            }

            Instruction::TestEQ { test, dst }
            | Instruction::TestNE { test, dst }
            | Instruction::TestGT { test, dst }
            | Instruction::TestGE { test, dst }
            | Instruction::TestLT { test, dst }
            | Instruction::TestLE { test, dst } => {
                writeln!(f, "    {} {} => {}", self.inst_name(), test, dst)
            }
            Instruction::ImmJump(label) => writeln!(f, "    {} -> {}", self.inst_name(), label),
            Instruction::Jump(reg) => writeln!(f, "    {} -> {}", self.inst_name(), reg),
            Instruction::Call { name, args } => writeln!(
                f,
                "    {} {}{} {}",
                self.inst_name(),
                name,
                if args.is_empty() { "" } else { "," },
                args.iter().map(|r| r.to_string()).collect::<Vec<_>>().join(", ")
            ),
            Instruction::ImmCall { name, args, ret } => writeln!(
                f,
                "    {} {}, {} => {}",
                self.inst_name(),
                name,
                args.iter().map(|r| r.to_string()).collect::<Vec<_>>().join(", "),
                ret
            ),
            Instruction::ImmRCall { reg, args, ret } => writeln!(
                f,
                "    {} {}, {} => {}",
                self.inst_name(),
                reg,
                args.iter().map(|r| r.to_string()).collect::<Vec<_>>().join(", "),
                ret
            ),
            Instruction::ImmRet(reg) => writeln!(f, "    {} {}", self.inst_name(), reg),
            Instruction::CbrT { cond, loc } | Instruction::CbrF { cond, loc } => {
                writeln!(f, "    {} {} -> {}", self.inst_name(), cond, loc)
            }
            Instruction::CbrLT { a, b, loc }
            | Instruction::CbrLE { a, b, loc }
            | Instruction::CbrGT { a, b, loc }
            | Instruction::CbrGE { a, b, loc }
            | Instruction::CbrEQ { a, b, loc }
            | Instruction::CbrNE { a, b, loc } => {
                writeln!(f, "    {} {}, {} -> {}", self.inst_name(), a, b, loc)
            }

            Instruction::FAdd { src_a, src_b, dst }
            | Instruction::FSub { src_a, src_b, dst }
            | Instruction::FMult { src_a, src_b, dst }
            | Instruction::FDiv { src_a, src_b, dst }
            | Instruction::FComp { src_a, src_b, dst } => {
                writeln!(f, "    {} {}, {} => {}", self.inst_name(), src_a, src_b, dst)
            }

            Instruction::FLoadAddImm { src, add, dst } => {
                writeln!(f, "    {} {}, {} => {}", self.inst_name(), src, add, dst)
            }
            Instruction::FLoadAdd { src, add, dst } => {
                writeln!(f, "    {} {}, {} => {}", self.inst_name(), src, add, dst)
            }
            Instruction::FRead(reg)
            | Instruction::IRead(reg)
            | Instruction::FWrite(reg)
            | Instruction::IWrite(reg)
            | Instruction::SWrite(reg)
            | Instruction::PushR(reg) => writeln!(f, "    {} {}", self.inst_name(), reg),

            Instruction::Push(val) => writeln!(f, "    {} {}", self.inst_name(), val),
            Instruction::Frame { name, size, params } => {
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
            Instruction::Global { name, size, align } => {
                writeln!(f, "    .{} {}, {}, {}", self.inst_name(), name, size, align)
            }
            Instruction::String { name, content } => {
                writeln!(f, "    .{} {}, {}", self.inst_name(), name, content)
            }
            Instruction::Float { name, content } => {
                writeln!(f, "    .{} {}, {}", self.inst_name(), name, content)
            }
            Instruction::Label(label) => {
                writeln!(f, "{} nop", label)
            }
            Instruction::Text | Instruction::Data => writeln!(f, "    .{}", self.inst_name()),
            Instruction::Skip(s) => writeln!(f, "    # {}", s.trim()),
            Instruction::Phi(reg, s, sub) => writeln!(
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
    pub fn remove_phis(&mut self) {
        match self {
            Instruction::FLoad { src, dst }
            | Instruction::F2I { src, dst }
            | Instruction::I2F { src, dst }
            | Instruction::F2F { src, dst }
            | Instruction::I2I { src, dst }
            | Instruction::Not { src, dst }
            | Instruction::Load { src, dst }
            | Instruction::Store { src, dst } => {
                src.remove_phi();
                dst.remove_phi();
            }
            Instruction::Add { src_a, src_b, dst }
            | Instruction::Sub { src_a, src_b, dst }
            | Instruction::Mult { src_a, src_b, dst }
            | Instruction::Div { src_a, src_b, dst }
            | Instruction::LShift { src_a, src_b, dst }
            | Instruction::RShift { src_a, src_b, dst }
            | Instruction::Mod { src_a, src_b, dst }
            | Instruction::And { src_a, src_b, dst }
            | Instruction::Or { src_a, src_b, dst } => {
                src_a.remove_phi();
                src_b.remove_phi();
                dst.remove_phi();
            }
            Instruction::ImmAdd { src, dst, .. }
            | Instruction::ImmSub { src, dst, .. }
            | Instruction::ImmMult { src, dst, .. }
            | Instruction::ImmLShift { src, dst, .. }
            | Instruction::ImmRShift { src, dst, .. } => {
                src.remove_phi();
                dst.remove_phi();
            }

            Instruction::ImmLoad { dst, .. } => {
                dst.remove_phi();
            }
            Instruction::LoadAddImm { src, dst, .. }
            | Instruction::StoreAddImm { src, dst, .. } => {
                src.remove_phi();
                dst.remove_phi();
            }
            Instruction::LoadAdd { src, add, dst } | Instruction::StoreAdd { src, add, dst } => {
                src.remove_phi();
                add.remove_phi();
                dst.remove_phi();
            }

            Instruction::CmpLT { a, b, dst }
            | Instruction::CmpLE { a, b, dst }
            | Instruction::CmpGT { a, b, dst }
            | Instruction::CmpGE { a, b, dst }
            | Instruction::CmpEQ { a, b, dst }
            | Instruction::CmpNE { a, b, dst }
            | Instruction::Comp { a, b, dst } => {
                a.remove_phi();
                b.remove_phi();
                dst.remove_phi();
            }

            Instruction::TestEQ { test, dst }
            | Instruction::TestNE { test, dst }
            | Instruction::TestGT { test, dst }
            | Instruction::TestGE { test, dst }
            | Instruction::TestLT { test, dst }
            | Instruction::TestLE { test, dst } => {
                test.remove_phi();
                dst.remove_phi();
            }
            Instruction::ImmJump(..) => {}
            Instruction::Jump(reg) => reg.remove_phi(),
            Instruction::Call { args, .. } => {
                for arg in args {
                    arg.remove_phi();
                }
            }
            Instruction::ImmCall { args, ret, .. } => {
                ret.remove_phi();
                for arg in args {
                    arg.remove_phi();
                }
            }
            Instruction::ImmRCall { reg, args, ret } => {
                reg.remove_phi();
                ret.remove_phi();
                for arg in args {
                    arg.remove_phi();
                }
            }
            Instruction::ImmRet(reg) => reg.remove_phi(),
            Instruction::CbrT { cond, .. } | Instruction::CbrF { cond, .. } => {
                cond.remove_phi();
            }
            Instruction::CbrLT { a, b, .. }
            | Instruction::CbrLE { a, b, .. }
            | Instruction::CbrGT { a, b, .. }
            | Instruction::CbrGE { a, b, .. }
            | Instruction::CbrEQ { a, b, .. }
            | Instruction::CbrNE { a, b, .. } => {
                a.remove_phi();
                b.remove_phi();
            }

            Instruction::FAdd { src_a, src_b, dst }
            | Instruction::FSub { src_a, src_b, dst }
            | Instruction::FMult { src_a, src_b, dst }
            | Instruction::FDiv { src_a, src_b, dst }
            | Instruction::FComp { src_a, src_b, dst } => {
                src_a.remove_phi();
                src_b.remove_phi();
                dst.remove_phi();
            }

            Instruction::FLoadAddImm { src, dst, .. } => {
                src.remove_phi();
                dst.remove_phi();
            }
            Instruction::FLoadAdd { src, add, dst } => {
                src.remove_phi();
                add.remove_phi();
                dst.remove_phi();
            }
            Instruction::FRead(reg)
            | Instruction::IRead(reg)
            | Instruction::FWrite(reg)
            | Instruction::IWrite(reg)
            | Instruction::SWrite(reg)
            | Instruction::PushR(reg) => reg.remove_phi(),

            Instruction::Push(..) => {}
            Instruction::Frame { params, .. } => {
                for arg in params {
                    arg.remove_phi();
                }
            }
            Instruction::Global { .. } => {}
            Instruction::String { .. } => {}
            Instruction::Float { .. } => {}
            Instruction::Label(..) => {}
            Instruction::Text | Instruction::Data => {}
            Instruction::Skip(..) => {}
            Instruction::Phi(..) => {
                *self = Instruction::Skip(format!("{}", self));
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
            Instruction::I2I { dst, .. } => Some(dst),
            Instruction::F2I { dst, .. } => Some(dst),
            Instruction::I2F { dst, .. } => Some(dst),
            Instruction::F2F { dst, .. } => Some(dst),
            Instruction::Add { dst, .. } => Some(dst),
            Instruction::Sub { dst, .. } => Some(dst),
            Instruction::Mult { dst, .. } => Some(dst),
            Instruction::LShift { dst, .. } => Some(dst),
            Instruction::RShift { dst, .. } => Some(dst),
            Instruction::Mod { dst, .. } => Some(dst),
            Instruction::And { dst, .. } => Some(dst),
            Instruction::Or { dst, .. } => Some(dst),
            Instruction::Not { dst, .. } => Some(dst),
            Instruction::ImmAdd { dst, .. } => Some(dst),
            Instruction::ImmSub { dst, .. } => Some(dst),
            Instruction::ImmMult { dst, .. } => Some(dst),
            Instruction::ImmLShift { dst, .. } => Some(dst),
            Instruction::ImmRShift { dst, .. } => Some(dst),
            Instruction::CmpLT { dst, .. } => Some(dst),
            Instruction::CmpLE { dst, .. } => Some(dst),
            Instruction::CmpGT { dst, .. } => Some(dst),
            Instruction::CmpGE { dst, .. } => Some(dst),
            Instruction::CmpEQ { dst, .. } => Some(dst),
            Instruction::CmpNE { dst, .. } => Some(dst),
            Instruction::Comp { dst, .. } => Some(dst),
            Instruction::TestEQ { dst, .. } => Some(dst),
            Instruction::TestNE { dst, .. } => Some(dst),
            Instruction::TestGT { dst, .. } => Some(dst),
            Instruction::TestGE { dst, .. } => Some(dst),
            Instruction::TestLT { dst, .. } => Some(dst),
            Instruction::TestLE { dst, .. } => Some(dst),
            // Float stuff
            Instruction::FAdd { dst, .. } => Some(dst),
            Instruction::FSub { dst, .. } => Some(dst),
            Instruction::FMult { dst, .. } => Some(dst),
            Instruction::FDiv { dst, .. } => Some(dst),
            Instruction::FComp { dst, .. } => Some(dst),

            // Loads
            Instruction::ImmLoad { dst, .. }
            | Instruction::Load { dst, .. }
            | Instruction::LoadAddImm { dst, .. }
            | Instruction::LoadAdd { dst, .. }
            | Instruction::FLoad { dst, .. }
            | Instruction::FLoadAddImm { dst, .. }
            | Instruction::FLoadAdd { dst, .. } => Some(dst),
            // Call with return `call arg, arg => ret`
            Instruction::ImmCall { ret, .. } => Some(ret),
            Instruction::ImmRCall { ret, .. } => Some(ret),
            _ => None,
        }
    }
    pub fn target_reg_mut(&mut self) -> Option<&mut Reg> {
        match self {
            // Instruction::Store { dst, .. } => Some(dst),
            // Instruction::StoreAddImm { dst, .. } => Some(dst),
            // Instruction::StoreAdd { dst, .. } => Some(dst),
            // Instruction::IWrite(dst) => Some(dst),
            // Instruction::SWrite(dst) => Some(dst),
            // Instruction::FWrite(dst) => Some(dst),
            // Instruction::IRead(dst) => Some(dst),
            // Instruction::FRead(dst) => Some(dst),
            Instruction::I2I { dst, .. }
            | Instruction::I2F { dst, .. }
            | Instruction::Add { dst, .. }
            | Instruction::Sub { dst, .. }
            | Instruction::Mult { dst, .. }
            | Instruction::LShift { dst, .. }
            | Instruction::RShift { dst, .. }
            | Instruction::Mod { dst, .. }
            | Instruction::And { dst, .. }
            | Instruction::Or { dst, .. }
            | Instruction::Not { dst, .. }
            | Instruction::ImmAdd { dst, .. }
            | Instruction::ImmSub { dst, .. }
            | Instruction::ImmMult { dst, .. }
            | Instruction::ImmLShift { dst, .. }
            | Instruction::ImmRShift { dst, .. }
            | Instruction::ImmLoad { dst, .. }
            | Instruction::Load { dst, .. }
            | Instruction::LoadAddImm { dst, .. }
            | Instruction::LoadAdd { dst, .. }
            | Instruction::CmpLT { dst, .. }
            | Instruction::CmpLE { dst, .. }
            | Instruction::CmpGT { dst, .. }
            | Instruction::CmpGE { dst, .. }
            | Instruction::CmpEQ { dst, .. }
            | Instruction::CmpNE { dst, .. }
            | Instruction::Comp { dst, .. }
            | Instruction::TestEQ { dst, .. }
            | Instruction::TestNE { dst, .. }
            | Instruction::TestGT { dst, .. }
            | Instruction::TestGE { dst, .. }
            | Instruction::TestLT { dst, .. }
            | Instruction::TestLE { dst, .. }
            | Instruction::F2I { dst, .. }
            | Instruction::F2F { dst, .. }
            | Instruction::FAdd { dst, .. }
            | Instruction::FSub { dst, .. }
            | Instruction::FMult { dst, .. }
            | Instruction::FDiv { dst, .. }
            | Instruction::FComp { dst, .. }
            | Instruction::FLoad { dst, .. }
            | Instruction::FLoadAddImm { dst, .. }
            | Instruction::FLoadAdd { dst, .. } => Some(dst),
            // Call with return `call arg, arg => ret`
            Instruction::ImmCall { ret, .. } => Some(ret),
            Instruction::ImmRCall { ret, .. } => Some(ret),
            _ => None,
        }
    }

    /// The return value is (left, right) `Option<Operand>`.
    pub fn operands(&self) -> (Option<Operand>, Option<Operand>) {
        match self {
            Instruction::I2I { src, .. }
            | Instruction::Not { src, .. }
            | Instruction::Load { src, .. }
            | Instruction::F2I { src, .. }
            | Instruction::I2F { src, .. }
            | Instruction::F2F { src, .. } => (Some(Operand::Register(*src)), None),

            Instruction::Add { src_a, src_b, .. }
            | Instruction::Sub { src_a, src_b, .. }
            | Instruction::Mult { src_a, src_b, .. }
            | Instruction::LShift { src_a, src_b, .. }
            | Instruction::RShift { src_a, src_b, .. }
            | Instruction::Mod { src_a, src_b, .. }
            | Instruction::And { src_a, src_b, .. }
            | Instruction::Or { src_a, src_b, .. } => {
                (Some(Operand::Register(*src_a)), Some(Operand::Register(*src_b)))
            }
            Instruction::ImmAdd { src, konst, .. }
            | Instruction::ImmSub { src, konst, .. }
            | Instruction::ImmMult { src, konst, .. }
            | Instruction::ImmLShift { src, konst, .. }
            | Instruction::ImmRShift { src, konst, .. } => {
                (Some(Operand::Register(*src)), Some(Operand::Value(konst.clone())))
            }
            Instruction::ImmLoad { src, .. } => (Some(Operand::Value(src.clone())), None),
            Instruction::LoadAddImm { src, add, .. } => {
                (Some(Operand::Register(*src)), Some(Operand::Value(add.clone())))
            }
            Instruction::LoadAdd { src, add, .. } => {
                (Some(Operand::Register(*src)), Some(Operand::Register(*add)))
            }
            Instruction::Store { src, dst } => {
                (Some(Operand::Register(*src)), Some(Operand::Register(*dst)))
            }
            Instruction::StoreAddImm { src, add, .. } => {
                (Some(Operand::Register(*src)), Some(Operand::Value(add.clone())))
            }
            Instruction::StoreAdd { src, add, .. } => {
                (Some(Operand::Register(*src)), Some(Operand::Register(*add)))
            }
            Instruction::IWrite(r) | Instruction::FWrite(r) | Instruction::SWrite(r) => {
                (Some(Operand::Register(*r)), None)
            }
            Instruction::IRead(r) | Instruction::FRead(r) => (Some(Operand::Register(*r)), None),
            Instruction::CmpLT { a, b, .. }
            | Instruction::CmpLE { a, b, .. }
            | Instruction::CmpGT { a, b, .. }
            | Instruction::CmpGE { a, b, .. }
            | Instruction::CmpEQ { a, b, .. }
            | Instruction::CmpNE { a, b, .. }
            | Instruction::Comp { a, b, .. } => {
                (Some(Operand::Register(*a)), Some(Operand::Register(*b)))
            }
            Instruction::CbrT { cond, .. } | Instruction::CbrF { cond, .. } => {
                (Some(Operand::Register(*cond)), None)
            }
            Instruction::CbrEQ { a, b, .. }
            | Instruction::CbrNE { a, b, .. }
            | Instruction::CbrGT { a, b, .. }
            | Instruction::CbrGE { a, b, .. }
            | Instruction::CbrLT { a, b, .. }
            | Instruction::CbrLE { a, b, .. } => {
                (Some(Operand::Register(*a)), Some(Operand::Register(*b)))
            }
            Instruction::TestEQ { test, .. }
            | Instruction::TestNE { test, .. }
            | Instruction::TestGT { test, .. }
            | Instruction::TestGE { test, .. }
            | Instruction::TestLT { test, .. }
            | Instruction::TestLE { test, .. } => (Some(Operand::Register(*test)), None),

            Instruction::FAdd { src_a, src_b, .. }
            | Instruction::FSub { src_a, src_b, .. }
            | Instruction::FMult { src_a, src_b, .. }
            | Instruction::FDiv { src_a, src_b, .. }
            | Instruction::FComp { src_a, src_b, .. } => {
                (Some(Operand::Register(*src_a)), Some(Operand::Register(*src_b)))
            }
            Instruction::FLoad { src, .. } => (Some(Operand::Register(*src)), None),
            Instruction::FLoadAddImm { src, add, .. } => {
                (Some(Operand::Register(*src)), Some(Operand::Value(add.clone())))
            }
            Instruction::FLoadAdd { src, add, .. } => {
                (Some(Operand::Register(*src)), Some(Operand::Register(*add)))
            }
            Instruction::ImmRet(ret) => (Some(Operand::Register(*ret)), None),

            _ => (None, None),
        }
    }

    /// The return value is (left, right) `Option<&mut Reg>`.
    pub fn operands_mut(&mut self) -> (Option<&mut Reg>, Option<&mut Reg>) {
        match self {
            Instruction::I2I { src, .. }
            | Instruction::Not { src, .. }
            | Instruction::F2I { src, .. }
            | Instruction::I2F { src, .. }
            | Instruction::F2F { src, .. } => (Some(src), None),
            Instruction::Add { src_a, src_b, .. }
            | Instruction::Sub { src_a, src_b, .. }
            | Instruction::Mult { src_a, src_b, .. }
            | Instruction::LShift { src_a, src_b, .. }
            | Instruction::RShift { src_a, src_b, .. }
            | Instruction::Mod { src_a, src_b, .. }
            | Instruction::And { src_a, src_b, .. }
            | Instruction::Or { src_a, src_b, .. } => (Some(src_a), Some(src_b)),
            Instruction::ImmAdd { src, .. }
            | Instruction::ImmSub { src, .. }
            | Instruction::ImmMult { src, .. }
            | Instruction::ImmLShift { src, .. }
            | Instruction::ImmRShift { src, .. }
            | Instruction::Load { src, .. }
            | Instruction::LoadAddImm { src, .. }
            | Instruction::Store { src, .. }
            | Instruction::StoreAddImm { src, .. } => (Some(src), None),
            Instruction::LoadAdd { src, add, .. } | Instruction::StoreAdd { src, add, .. } => {
                (Some(src), Some(add))
            }
            Instruction::IWrite(r)
            | Instruction::SWrite(r)
            | Instruction::FWrite(r)
            | Instruction::IRead(r)
            | Instruction::FRead(r) => (Some(r), None),
            Instruction::CmpLT { a, b, .. }
            | Instruction::CmpLE { a, b, .. }
            | Instruction::CmpGT { a, b, .. }
            | Instruction::CmpGE { a, b, .. }
            | Instruction::CmpEQ { a, b, .. }
            | Instruction::CmpNE { a, b, .. }
            | Instruction::Comp { a, b, .. } => (Some(a), Some(b)),
            Instruction::CbrT { cond, .. } | Instruction::CbrF { cond, .. } => (Some(cond), None),
            Instruction::CbrLT { a, b, .. }
            | Instruction::CbrLE { a, b, .. }
            | Instruction::CbrGT { a, b, .. }
            | Instruction::CbrGE { a, b, .. }
            | Instruction::CbrEQ { a, b, .. }
            | Instruction::CbrNE { a, b, .. } => (Some(a), Some(b)),
            Instruction::TestEQ { test, .. }
            | Instruction::TestNE { test, .. }
            | Instruction::TestGT { test, .. }
            | Instruction::TestGE { test, .. }
            | Instruction::TestLT { test, .. }
            | Instruction::TestLE { test, .. } => (Some(test), None),

            Instruction::FAdd { src_a, src_b, .. }
            | Instruction::FSub { src_a, src_b, .. }
            | Instruction::FMult { src_a, src_b, .. }
            | Instruction::FDiv { src_a, src_b, .. }
            | Instruction::FComp { src_a, src_b, .. } => (Some(src_a), Some(src_b)),
            Instruction::FLoad { src, .. } => (Some(src), None),
            Instruction::FLoadAddImm { src, add: _, .. } => (Some(src), None),
            Instruction::FLoadAdd { src, add, .. } => (Some(src), Some(add)),
            Instruction::ImmRet(ret) => (Some(ret), None),
            _ => (None, None),
        }
    }

    pub const fn inst_name(&self) -> &'static str {
        match self {
            Instruction::I2I { .. } => "i2i",
            Instruction::Add { .. } => "add",
            Instruction::Sub { .. } => "sub",
            Instruction::Mult { .. } => "mult",
            Instruction::Div { .. } => "div",
            Instruction::LShift { .. } => "lshift",
            Instruction::RShift { .. } => "rshift",
            Instruction::Mod { .. } => "mod",
            Instruction::And { .. } => "and",
            Instruction::Or { .. } => "or",
            Instruction::Not { .. } => "not",
            Instruction::ImmAdd { .. } => "addI",
            Instruction::ImmSub { .. } => "subI",
            Instruction::ImmMult { .. } => "multI",
            Instruction::ImmLShift { .. } => "lshiftI",
            Instruction::ImmRShift { .. } => "rshiftI",
            Instruction::ImmLoad { .. } => "loadI",
            Instruction::Load { .. } => "load",
            Instruction::LoadAddImm { .. } => "loadAI",
            Instruction::LoadAdd { .. } => "loadAO",
            Instruction::Store { .. } => "store",
            Instruction::StoreAddImm { .. } => "storeAI",
            Instruction::StoreAdd { .. } => "storeAO",
            Instruction::CmpLT { .. } => "cmp_LT",
            Instruction::CmpLE { .. } => "cmp_LE",
            Instruction::CmpGT { .. } => "cmp_GT",
            Instruction::CmpGE { .. } => "cmp_GE",
            Instruction::CmpEQ { .. } => "cmp_EQ",
            Instruction::CmpNE { .. } => "cmp_NE",
            Instruction::Comp { .. } => "comp",
            Instruction::TestEQ { .. } => "testeq",
            Instruction::TestNE { .. } => "testne",
            Instruction::TestGT { .. } => "testgt",
            Instruction::TestGE { .. } => "testge",
            Instruction::TestLT { .. } => "testlt",
            Instruction::TestLE { .. } => "testle",
            Instruction::ImmJump(_) => "jumpI",
            Instruction::Jump(_) => "jump",
            Instruction::Call { .. } => "call",
            Instruction::ImmCall { .. } => "icall",
            Instruction::ImmRCall { .. } => "ircall",
            Instruction::Ret => "ret",
            Instruction::ImmRet(_) => "iret",
            Instruction::CbrT { .. } => "cbr",
            Instruction::CbrF { .. } => "cbrne",
            Instruction::CbrLT { .. } => "cbr_LT",
            Instruction::CbrLE { .. } => "cbr_LE",
            Instruction::CbrGT { .. } => "cbr_GT",
            Instruction::CbrGE { .. } => "cbr_GE",
            Instruction::CbrEQ { .. } => "cbr_EQ",
            Instruction::CbrNE { .. } => "cbr_NE",
            Instruction::F2I { .. } => "f2i",
            Instruction::I2F { .. } => "i2f",
            Instruction::F2F { .. } => "f2f",
            Instruction::FAdd { .. } => "fadd",
            Instruction::FSub { .. } => "fsub",
            Instruction::FMult { .. } => "fmult",
            Instruction::FDiv { .. } => "fdiv",
            Instruction::FComp { .. } => "fcomp",
            Instruction::FLoad { .. } => "fload",
            Instruction::FLoadAddImm { .. } => "floadAI",
            Instruction::FLoadAdd { .. } => "floadAO",
            Instruction::FRead(_) => "fread",
            Instruction::IRead(_) => "iread",
            Instruction::FWrite(_) => "fwrite",
            Instruction::IWrite(_) => "iwrite",
            Instruction::SWrite(_) => "swrite",
            Instruction::Push(_) => "push",
            Instruction::PushR(_) => "pushr",
            Instruction::Pop => "pop",
            Instruction::Data => "data",
            Instruction::Text => "text",
            Instruction::Frame { .. } => "frame",
            Instruction::Global { .. } => "global",
            Instruction::String { .. } => "string",
            Instruction::Float { .. } => "float",
            Instruction::Label(_) => "label",
            Instruction::Skip(..) | Instruction::Phi(..) => {
                panic!("should never print a skip or phi instruction")
            }
        }
    }

    pub fn uses_label(&self) -> Option<&str> {
        match self {
            Instruction::ImmJump(loc)
            | Instruction::CbrT { loc, .. }
            | Instruction::CbrF { loc, .. }
            | Instruction::CbrLT { loc, .. }
            | Instruction::CbrLE { loc, .. }
            | Instruction::CbrGT { loc, .. }
            | Instruction::CbrGE { loc, .. }
            | Instruction::CbrEQ { loc, .. }
            | Instruction::CbrNE { loc, .. } => Some(&loc.0),
            _ => None,
        }
    }

    pub fn label_mut(&mut self) -> Option<&mut Loc> {
        match self {
            Instruction::ImmJump(loc)
            | Instruction::CbrT { loc, .. }
            | Instruction::CbrF { loc, .. }
            | Instruction::CbrLT { loc, .. }
            | Instruction::CbrLE { loc, .. }
            | Instruction::CbrGT { loc, .. }
            | Instruction::CbrGE { loc, .. }
            | Instruction::CbrEQ { loc, .. }
            | Instruction::CbrNE { loc, .. } => Some(loc),
            _ => None,
        }
    }

    pub fn is_cnd_jump(&self) -> bool {
        matches!(
            self,
            Instruction::CbrT { .. }
                | Instruction::CbrF { .. }
                | Instruction::CbrLT { .. }
                | Instruction::CbrLE { .. }
                | Instruction::CbrGT { .. }
                | Instruction::CbrGE { .. }
                | Instruction::CbrEQ { .. }
                | Instruction::CbrNE { .. }
        )
    }

    pub fn unconditional_jmp(&self) -> bool {
        matches!(self, Instruction::ImmJump(..) | Instruction::Ret | Instruction::ImmRet(_))
    }

    pub fn is_return(&self) -> bool {
        matches!(self, Instruction::Ret | Instruction::ImmRet(_))
    }

    pub fn as_new_move_instruction(&self, src: Reg, dst: Reg) -> Instruction {
        match self {
            Instruction::I2I { .. }
            | Instruction::Add { .. }
            | Instruction::Sub { .. }
            | Instruction::Mult { .. }
            | Instruction::LShift { .. }
            | Instruction::RShift { .. }
            | Instruction::Mod { .. }
            | Instruction::And { .. }
            | Instruction::Or { .. }
            | Instruction::Not { .. }
            | Instruction::ImmAdd { .. }
            | Instruction::ImmSub { .. }
            | Instruction::ImmMult { .. }
            | Instruction::ImmLShift { .. }
            | Instruction::ImmRShift { .. }
            | Instruction::ImmLoad { .. }
            | Instruction::Load { .. }
            | Instruction::LoadAddImm { .. }
            | Instruction::LoadAdd { .. } => Instruction::I2I { src, dst },
            Instruction::F2I { .. }
            | Instruction::I2F { .. }
            | Instruction::F2F { .. }
            | Instruction::FAdd { .. }
            | Instruction::FSub { .. }
            | Instruction::FMult { .. }
            | Instruction::FDiv { .. }
            | Instruction::FComp { .. }
            | Instruction::FLoad { .. }
            | Instruction::FLoadAddImm { .. }
            | Instruction::FLoadAdd { .. } => Instruction::F2F { src, dst },
            Self::Store { .. } | Self::StoreAddImm { .. } | Self::IRead(_) | Self::FRead(_) => {
                unreachable!("cannot simplify store instruction")
            }
            _ => unreachable!(
                "stack, text/data section stuff, calls, jumps, and comp/test stuff {:?}",
                self
            ),
        }
    }

    pub fn fold(&self, a: &Val, b: &Val) -> Option<Instruction> {
        Some(match (a, b) {
            (Val::Integer(a), Val::Integer(b)) => match self {
                Instruction::Add { dst, .. } => {
                    Instruction::ImmLoad { src: Val::Integer(a + b), dst: *dst }
                }
                Instruction::Sub { dst, .. } => {
                    Instruction::ImmLoad { src: Val::Integer(a - b), dst: *dst }
                }
                Instruction::Mult { dst, .. } => {
                    Instruction::ImmLoad { src: Val::Integer(a * b), dst: *dst }
                }
                Instruction::LShift { dst, .. } => {
                    Instruction::ImmLoad { src: Val::Integer(a << b), dst: *dst }
                }
                Instruction::RShift { dst, .. } => {
                    Instruction::ImmLoad { src: Val::Integer(a >> b), dst: *dst }
                }
                Instruction::Mod { dst, .. } if *b != 0 => {
                    Instruction::ImmLoad { src: Val::Integer(a % b), dst: *dst }
                }
                Instruction::And { dst, .. } => {
                    Instruction::ImmLoad { src: Val::Integer(a & b), dst: *dst }
                }
                Instruction::Or { dst, .. } => {
                    Instruction::ImmLoad { src: Val::Integer(a | b), dst: *dst }
                }
                _ => {
                    return None;
                }
            },
            (Val::Float(_), Val::Float(_)) => match self {
                Instruction::F2F { dst: _, .. }
                | Instruction::FAdd { dst: _, .. }
                | Instruction::FSub { dst: _, .. }
                | Instruction::FMult { dst: _, .. }
                | Instruction::FDiv { dst: _, .. }
                | Instruction::FComp { dst: _, .. } => todo!(),
                _ => {
                    return None;
                }
            },
            _ => {
                return None;
            }
        })
    }

    pub fn fold_two_address(&self, a: &Val) -> Option<Instruction> {
        Some(match self {
            Instruction::Load { dst, .. } => Instruction::ImmLoad { src: a.clone(), dst: *dst },
            Instruction::I2I { dst, .. } => Instruction::ImmLoad { src: a.clone(), dst: *dst },
            _ => {
                return None;
            }
        })
    }

    /// If this operation is an identity operation, return the register that would be unchanged.
    ///
    /// `add %vr2, 0 => %vr3` is the same as `i2i %vr2 => %vr3`
    ///
    /// TODO:
    /// 2 * a = a + a, a / 1 = a, a / a = 1 if a != 0,
    /// a >> 0 = a, a << 0 = a, a && a = a, a || a = a
    pub fn identity_register(&self) -> Option<Reg> {
        Some(match self {
            Instruction::Add { .. } | Instruction::FAdd { .. } => match self.operands() {
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
            Instruction::Sub { .. } | Instruction::FSub { .. } => match self.operands() {
                (Some(Operand::Register(reg)), Some(Operand::Value(val))) if val.is_zero() => reg,
                (Some(Operand::Register(a)), Some(Operand::Register(b))) if a == b => {
                    todo!("this is sub id 0")
                }
                _ => {
                    return None;
                }
            },
            Instruction::Mult { .. } | Instruction::FMult { .. } => match self.operands() {
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
            Instruction::FDiv { .. } => match self.operands() {
                (Some(Operand::Register(reg)), Some(Operand::Value(val))) if val.is_one() => reg,
                (Some(Operand::Register(a)), Some(Operand::Register(b))) if a == b => {
                    todo!("this is div id 1")
                }
                _ => {
                    return None;
                }
            },
            Instruction::LShift { .. } | Instruction::RShift { .. } => match self.operands() {
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
            Instruction::Mod { .. } => match self.operands() {
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
            Instruction::And { .. } => match self.operands() {
                (Some(Operand::Register(a)), Some(Operand::Register(b))) if a == b => a,
                _ => {
                    return None;
                }
            },
            Instruction::Or { dst: _, .. } => match self.operands() {
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

    /// If this operation is an identity operation, return the register that would be unchanged.
    /// `val` is always the left operand, subtraction is __never__ a valid identity op for this
    /// call.
    ///
    /// `add %vr2, 0 => %vr3` is the same as `i2i %vr2 => %vr3`
    pub fn identity_with_const_prop_left(&self, val: &Val) -> Option<&Reg> {
        Some(match self {
            Instruction::Add { src_b, .. } | Instruction::FAdd { src_b, .. } if val.is_zero() => {
                src_b
            }
            Instruction::Mult { src_b, .. } | Instruction::FMult { src_b, .. } if val.is_one() => {
                src_b
            }
            Instruction::And { .. } => todo!(),
            Instruction::Or { dst: _, .. } => todo!(),
            _ => {
                return None;
            }
        })
    }

    /// If this operation is an identity operation, return the register that would be unchanged.
    /// `val` is always the right operand, subtraction is a valid identity op.
    ///
    /// `add %vr2, 0 => %vr3` is the same as `i2i %vr2 => %vr3`
    pub fn identity_with_const_prop_right(&self, val: &Val) -> Option<&Reg> {
        Some(match self {
            Instruction::Add { src_a, .. } | Instruction::FAdd { src_a, .. } if val.is_zero() => {
                src_a
            }
            Instruction::Sub { src_a, .. } | Instruction::FSub { src_a, .. } if val.is_zero() => {
                src_a
            }
            Instruction::Mult { src_a, .. } | Instruction::FMult { src_a, .. } if val.is_one() => {
                src_a
            }
            Instruction::FDiv { src_a, .. } if val.is_one() => src_a,
            Instruction::Mod { src_a, .. } if val.is_one() => src_a,
            Instruction::LShift { src_a, .. } if val.is_zero() => src_a,
            Instruction::RShift { src_a, .. } if val.is_zero() => src_a,
            Instruction::And { .. } => todo!(),
            Instruction::Or { dst: _, .. } => todo!(),
            _ => {
                return None;
            }
        })
    }

    pub fn as_immediate_instruction_right(&self, a: &Val) -> Option<Instruction> {
        Some(match self {
            Instruction::Add { src_a, dst, .. } => {
                Instruction::ImmAdd { src: *src_a, konst: a.clone(), dst: *dst }
            }
            Instruction::Sub { src_a, dst, .. } => {
                Instruction::ImmSub { src: *src_a, konst: a.clone(), dst: *dst }
            }
            Instruction::Mult { src_a, dst, .. } => {
                Instruction::ImmMult { src: *src_a, konst: a.clone(), dst: *dst }
            }
            Instruction::LShift { src_a, dst, .. } => {
                Instruction::ImmLShift { src: *src_a, konst: a.clone(), dst: *dst }
            }
            Instruction::RShift { src_a, dst, .. } => {
                Instruction::ImmRShift { src: *src_a, konst: a.clone(), dst: *dst }
            }
            Instruction::F2F { dst: _, .. }
            | Instruction::FAdd { dst: _, .. }
            | Instruction::FSub { dst: _, .. }
            | Instruction::FMult { dst: _, .. }
            | Instruction::FDiv { dst: _, .. }
            | Instruction::FComp { dst: _, .. } => todo!(),
            _ => {
                return None;
            }
        })
    }

    pub fn as_immediate_instruction_left(&self, a: &Val) -> Option<Instruction> {
        Some(match self {
            Instruction::Add { src_b, dst, .. } => {
                Instruction::ImmAdd { src: *src_b, konst: a.clone(), dst: *dst }
            }
            Instruction::Mult { src_b, dst, .. } => {
                Instruction::ImmMult { src: *src_b, konst: a.clone(), dst: *dst }
            }
            Instruction::ImmAdd { konst, dst, .. } => {
                Instruction::ImmLoad { src: a.add(konst)?, dst: *dst }
            }
            Instruction::ImmMult { konst, dst, .. } => {
                Instruction::ImmLoad { src: a.mult(konst)?, dst: *dst }
            }
            Instruction::RShift { src_a, dst, .. } => {
                Instruction::ImmRShift { src: *src_a, konst: a.clone(), dst: *dst }
            }
            Instruction::F2F { dst: _, .. }
            | Instruction::FAdd { dst: _, .. }
            | Instruction::FSub { dst: _, .. }
            | Instruction::FMult { dst: _, .. }
            | Instruction::FDiv { dst: _, .. }
            | Instruction::FComp { dst: _, .. } => todo!(),
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

    pub fn is_call_instruction(&self) -> bool {
        matches!(self, Self::Call { .. } | Self::ImmCall { .. } | Self::ImmRCall { .. })
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

    pub fn is_phi(&self) -> bool {
        matches!(self, Instruction::Phi(..))
    }

    pub fn is_tmp_expr(&self) -> bool {
        matches!(
            self,
            Self::Add { .. }
                | Self::Sub { .. }
                | Self::Mult { .. }
                | Self::LShift { .. }
                | Self::RShift { .. }
                | Self::Mod { .. }
                | Self::And { .. }
                | Self::Or { .. }
                | Self::Not { .. }
                | Self::ImmAdd { .. }
                | Self::ImmSub { .. }
                | Self::ImmMult { .. }
                | Self::ImmLShift { .. }
                | Self::ImmRShift { .. }
                | Self::FAdd { .. }
                | Self::FSub { .. }
                | Self::FMult { .. }
                | Self::ImmLoad { src: Val::Integer(..) | Val::Float(..), .. }
        )
    }
}

pub fn parse_text(input: &str) -> Result<Vec<Instruction>, &'static str> {
    let mut instructions = vec![];

    for line in input.lines() {
        let comp = line.split_ascii_whitespace().map(|s| s.replace(',', "")).collect::<Vec<_>>();
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

            // Memory operations
            ["loadI", src, "=>", dst] => instructions
                .push(Instruction::ImmLoad { src: Val::from_str(src)?, dst: Reg::from_str(dst)? }),
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
            ["storeAI", a, "=>", b, dst] => instructions.push(Instruction::StoreAddImm {
                src: Reg::from_str(a)?,
                add: Val::from_str(b)?,
                dst: Reg::from_str(dst)?,
            }),
            ["storeAO", a, "=>", b, dst] => instructions.push(Instruction::StoreAdd {
                src: Reg::from_str(a)?,
                add: Reg::from_str(b)?,
                dst: Reg::from_str(dst)?,
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
            [".global", name, size, align] => instructions.push(Instruction::Global {
                name: name.to_string(),
                size: size.parse().map_err(|_| "failed to parse .global size")?,
                align: align.parse().map_err(|_| "failed to parse .global align")?,
            }),
            [".string", name, str_lit] => instructions
                .push(Instruction::String { name: name.to_string(), content: str_lit.to_string() }),
            [".float", name, val] => instructions.push(Instruction::Float {
                name: name.to_string(),
                content: val.parse().map_err(|_| "failed to parse .float value")?,
            }),
            [label, "nop"] => instructions.push(Instruction::Label(label.to_string())),
            [first, ..] if first.starts_with('#') => {}
            [label] if label.starts_with('.') => {
                instructions.push(Instruction::Label(label.to_string()))
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
    /// All `Instruction`s with `Instruction::Skip` filtered out.
    pub fn instructions(&self) -> impl Iterator<Item = &Instruction> + '_ {
        self.instructions.iter().filter(|i| !matches!(i, Instruction::Skip(..)))
    }

    /// Returns the optional name of the block the conditional branch jumps to, the caller must find
    /// the fall through block name.
    pub fn ends_with_cond_branch(&self) -> Option<&str> {
        self.instructions.last().and_then(|i| i.is_cnd_jump().then(|| i.uses_label()).flatten())
    }
    /// Returns name a block a `jumpI` instruction goes to if block ends with jump immediate.
    pub fn ends_with_jump(&self) -> Option<&str> {
        match self.instructions.last() {
            Some(Instruction::ImmJump(l)) => Some(l.as_str()),
            _ => None,
        }
    }
}

#[derive(Debug)]
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
            let label = format!(".F_{}:", name);
            functions.push(Function {
                label: name.to_string(),
                stack_size: *size,
                params: params.clone(),
                blocks: vec![Block {
                    label: label.clone(),
                    instructions: vec![inst.clone(), Instruction::Label(label)],
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
        for blk in &func.blocks {
            blocks.push(Block { label: blk.label.clone(), instructions: vec![] });
            for (idx, inst) in blk.instructions.iter().enumerate() {
                // We always add the instruction even when it's a cbr/jmp with no block after
                blocks.last_mut().unwrap().instructions.push(inst.clone());

                if inst.is_cnd_jump() && !matches!(blk.instructions.get(idx + 1), None) {
                    let label = format!(".{}{}", blocks.len(), blk.label.replace('.', ""));

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
