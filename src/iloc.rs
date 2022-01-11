use std::{collections::HashMap, str::FromStr};

#[derive(Clone, Debug)]
pub enum Val {
    Integer(isize),
    Float(f64),
    Location(String),
}
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

#[derive(Clone, Copy, Debug)]
pub enum Reg {
    Expr(usize),
    Var(usize),
}

impl FromStr for Reg {
    type Err = &'static str;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Reg::Var(
            s.split("%vr")
                .last()
                .ok_or("no register number found")?
                .parse::<usize>()
                .map_err(|_| "`Reg` parse error")?,
        ))
    }
}

#[derive(Clone, Debug)]
pub struct Loc(String);

impl FromStr for Loc {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self(s.to_string()))
    }
}

#[rustfmt::skip]
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
    /// `call name %r, %r
    ImmCall { name: String, args: Vec<Reg>, ret: Reg },
    /// Call instruction, includes arguments and return register.
    /// `call name %r, %r
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
    /// `fstore`
    FStore { src_a: Reg, src_b: Reg, dst: Reg },
    /// `fstoreAI`
    FStoreAddImm { src: Reg, add: Val, dst: Reg },
    /// `fstoreAO`
    FStoreAdd { src: Reg, add: Reg, dst: Reg },

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
    /// Stack add `stadd`
    StAdd,
    /// `stsub`
    StSub,
    /// `stmul`
    StMul,
    /// `stdiv`
    StDiv,
    /// `stlshift`
    StLShift,
    /// `strshift`
    StRShift,
    /// `stcomp`
    StComp,
    /// `stand`
    StAnd,
    /// `stor`
    StOr,
    /// `stnot`
    StNot,
    /// `stload`
    StLoad,
    /// `ststore`
    StStore,
    /// `sttesteq`
    StTestEQ,
    /// `sttestne`
    StTestNE,
    /// `sttestgt`
    StTestGT,
    /// `sttestge`
    StTestGE,
    /// `sttestlt`
    StTestLT,
    /// `sttestle`
    StTestLE,
    /// `stfadd`
    StFAdd,
    /// `stfsub`
    StFSub,
    /// `stfmul`
    StFMul,
    /// `stfdiv`
    StFDiv,
    /// `stfcomp`
    StFComp,
    /// `stfload`
    StFLoad,
    /// `stfstore`
    StFStore,
    /// `stfread`
    StFRead,
    /// `stiread`
    StIRead,
    /// `stfwrite`
    StFWrite,
    /// `stiwrite`
    StIWrite,
    /// `stswrite`
    StSwrite,
    /// `stjump`
    StJump,

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
}

pub enum Operand<'a> {
    Register(&'a Reg),
    Location(&'a Loc),
    Value(&'a Val),
}

impl Instruction {
    // TODO: make another enum so this isn't so crappy
    // Have
    // enum Instruction {
    //     NoOperands(Inst),
    //     SingleOperand(Inst()),
    //     TwoOperand(Inst { src, dst }),
    // }
    /// Optional target register for 3 address instructions.
    pub fn target_reg(&self) -> Option<&Reg> {
        todo!()
    }

    /// The return value is (left, right) `Option<Operand<'_>>`.
    pub fn operands(&self) -> (Option<Operand<'_>>, Option<Operand<'_>>) {
        todo!()
    }

    pub fn inst_name(&self) -> &str {
        todo!()
    }
}

pub fn parse_text(input: &str) -> Result<Vec<Instruction>, &'static str> {
    let mut instructions = vec![];

    for line in input.lines() {
        let comp = line
            .split_ascii_whitespace()
            .map(|s| s.replace(',', ""))
            .collect::<Vec<_>>();
        if comp.is_empty() {
            continue;
        }

        match comp
            .iter()
            .map(|s| s.as_str())
            .collect::<Vec<_>>()
            .as_slice()
        {
            // Integer operations
            ["i2i", src, "=>", dst] => instructions.push(Instruction::I2I {
                src: Reg::from_str(src)?,
                dst: Reg::from_str(dst)?,
            }),
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
            ["and", a, b, "=>", dst] => instructions.push(Instruction::Add {
                src_a: Reg::from_str(a)?,
                src_b: Reg::from_str(b)?,
                dst: Reg::from_str(dst)?,
            }),
            ["or", a, b, "=>", dst] => instructions.push(Instruction::Or {
                src_a: Reg::from_str(a)?,
                src_b: Reg::from_str(b)?,
                dst: Reg::from_str(dst)?,
            }),
            ["not", src, "=>", dst] => instructions.push(Instruction::Not {
                src: Reg::from_str(src)?,
                dst: Reg::from_str(dst)?,
            }),
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
            ["loadI", src, "=>", dst] => instructions.push(Instruction::ImmLoad {
                src: Val::from_str(src)?,
                dst: Reg::from_str(dst)?,
            }),
            ["load", src, "=>", dst] => instructions.push(Instruction::Load {
                src: Reg::from_str(src)?,
                dst: Reg::from_str(dst)?,
            }),
            ["loadAI", a, b, "=>", dst] => instructions.push(Instruction::LoadAddImm {
                src: Reg::from_str(a)?,
                add: Val::from_str(b)?,
                dst: Reg::from_str(dst)?,
            }),
            ["loadA0", a, b, "=>", dst] => instructions.push(Instruction::LoadAdd {
                src: Reg::from_str(a)?,
                add: Reg::from_str(b)?,
                dst: Reg::from_str(dst)?,
            }),
            ["store", src, "=>", dst] => instructions.push(Instruction::Store {
                src: Reg::from_str(src)?,
                dst: Reg::from_str(dst)?,
            }),
            ["storeAI", a, b, "=>", dst] => instructions.push(Instruction::StoreAddImm {
                src: Reg::from_str(a)?,
                add: Val::from_str(b)?,
                dst: Reg::from_str(dst)?,
            }),
            ["storeA0", a, b, "=>", dst] => instructions.push(Instruction::StoreAdd {
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
            ["testeq", a, "=>", dst] => instructions.push(Instruction::TestEQ {
                test: Reg::from_str(a)?,
                dst: Reg::from_str(dst)?,
            }),
            ["testne", a, "=>", dst] => instructions.push(Instruction::TestNE {
                test: Reg::from_str(a)?,
                dst: Reg::from_str(dst)?,
            }),
            ["testgt", a, "=>", dst] => instructions.push(Instruction::TestGT {
                test: Reg::from_str(a)?,
                dst: Reg::from_str(dst)?,
            }),
            ["testge", a, "=>", dst] => instructions.push(Instruction::TestGE {
                test: Reg::from_str(a)?,
                dst: Reg::from_str(dst)?,
            }),
            ["testlt", a, "=>", dst] => instructions.push(Instruction::TestLT {
                test: Reg::from_str(a)?,
                dst: Reg::from_str(dst)?,
            }),
            ["testle", a, "=>", dst] => instructions.push(Instruction::TestLE {
                test: Reg::from_str(a)?,
                dst: Reg::from_str(dst)?,
            }),

            // Float operations
            ["f2i", src, "=>", dst] => instructions.push(Instruction::F2I {
                src: Reg::from_str(src)?,
                dst: Reg::from_str(dst)?,
            }),
            ["i2f", src, "=>", dst] => instructions.push(Instruction::I2F {
                src: Reg::from_str(src)?,
                dst: Reg::from_str(dst)?,
            }),
            ["f2f", src, "=>", dst] => instructions.push(Instruction::F2F {
                src: Reg::from_str(src)?,
                dst: Reg::from_str(dst)?,
            }),
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
            ["fload", a, "=>", dst] => instructions.push(Instruction::FLoad {
                src: Reg::from_str(a)?,
                dst: Reg::from_str(dst)?,
            }),
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
            ["store", a, "=>", dst] => instructions.push(Instruction::Store {
                src: Reg::from_str(a)?,
                dst: Reg::from_str(dst)?,
            }),
            ["storeAI", a, b, "=>", dst] => instructions.push(Instruction::StoreAddImm {
                src: Reg::from_str(a)?,
                add: Val::from_str(b)?,
                dst: Reg::from_str(dst)?,
            }),
            ["storeAO", a, b, "=>", dst] => instructions.push(Instruction::StoreAdd {
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
                instructions.push(Instruction::Call {
                    name: name.to_string(),
                    args,
                })
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
            ["cbr", src, "->", label] => instructions.push(Instruction::CbrT {
                cond: Reg::from_str(src)?,
                loc: Loc::from_str(label)?,
            }),
            ["cbrne", src, "->", label] => instructions.push(Instruction::CbrF {
                cond: Reg::from_str(src)?,
                loc: Loc::from_str(label)?,
            }),
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
            ["stadd"] => instructions.push(Instruction::StAdd),
            ["stsub"] => instructions.push(Instruction::StSub),
            ["stmul"] => instructions.push(Instruction::StMul),
            ["stdiv"] => instructions.push(Instruction::StDiv),
            ["stlshift"] => instructions.push(Instruction::StLShift),
            ["strshift"] => instructions.push(Instruction::StRShift),

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
            [".string", name, str_lit] => instructions.push(Instruction::String {
                name: name.to_string(),
                content: str_lit.to_string(),
            }),
            [".float", name, val] => instructions.push(Instruction::Float {
                name: name.to_string(),
                content: val.parse().map_err(|_| "failed to parse .float value")?,
            }),
            [label, "nop"] => instructions.push(Instruction::Label(label.to_string())),
            inst => todo!("{:?}", inst),
            // _ => {
            //     return Err("invalid instruction sequence");
            // }
        }
    }
    Ok(instructions)
}

#[derive(Debug)]
pub struct Block {
    pub label: String,
    /// Keep the instruction around for easy `to_string`ing.
    inst: Instruction,
    pub instructions: Vec<Instruction>,
}

#[derive(Debug)]
pub struct Function {
    pub label: String,
    /// Keep the instruction around for easy `to_string`ing.
    inst: Instruction,
    pub blk: Vec<Block>,
}

#[derive(Debug)]
pub struct IlocProgram {
    /// The .text and .data segments of an iloc program.
    pub preamble: Vec<Instruction>,
    /// Basic blocks.
    pub functions: Vec<Function>,
}

pub fn make_blks(iloc: Vec<Instruction>) -> IlocProgram {
    let fn_start = iloc
        .iter()
        .position(|inst| matches!(inst, Instruction::Frame { .. }))
        .unwrap_or_default();
    let (preamble, rest) = iloc.split_at(fn_start);

    let mut functions = vec![];
    let mut fn_idx = 0;
    let mut blk_idx = 0;
    for inst in rest {
        if let Instruction::Frame { name, .. } = inst {
            functions.push(Function {
                label: name.to_string(),
                inst: inst.clone(),
                blk: vec![Block {
                    label: format!(".L_{}", name),
                    inst: inst.clone(),
                    instructions: vec![],
                }],
            });
            fn_idx = functions.len().saturating_sub(1);
            blk_idx = 0;
        } else if let Instruction::Label(label) = inst {
            functions[fn_idx].blk.push(Block {
                label: label.to_string(),
                inst: inst.clone(),
                instructions: vec![],
            });
            blk_idx = functions[fn_idx].blk.len().saturating_sub(1);
        } else {
            functions[fn_idx].blk[blk_idx]
                .instructions
                .push(inst.clone());
        }
    }

    IlocProgram {
        preamble: preamble.to_vec(),
        functions,
    }
}

#[test]
fn parse_iloc() {
    use std::fs;

    let text = fs::read_to_string("./input/check.il").unwrap();
    parse_text(&text).unwrap();
}
