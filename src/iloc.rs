use std::{collections::HashMap, str::FromStr};

#[derive(Clone, Copy, Debug)]
pub struct Val(usize);
impl FromStr for Val {
    type Err = &'static str;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Val(s.parse::<usize>().map_err(|_| "`Val` parse error")?))
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
pub enum Loc {}

impl FromStr for Loc {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        todo!()
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
    /// `ret`
    Ret,
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
    F2I { src: Reg, dst: Reg },
    I2F { src: Reg, dst: Reg },
    F2F { src: Reg, dst: Reg },
    FAdd { src_a: Reg, src_b: Reg, dst: Reg },
    FSub { src_a: Reg, src_b: Reg, dst: Reg },
    FMult { src_a: Reg, src_b: Reg, dst: Reg },
    FDiv { src_a: Reg, src_b: Reg, dst: Reg },
    FComp { src_a: Reg, src_b: Reg, dst: Reg },
    FLoad { src_a: Reg, src_b: Reg, dst: Reg },
    FLoadAddImm { src: Reg, add: Val, dst: Reg },
    FLoadAdd { src: Reg, add: Reg, dst: Reg },
    FStore { src_a: Reg, src_b: Reg, dst: Reg },
    FStoreAddImm { src: Reg, add: Val, dst: Reg },
    FStoreAdd { src: Reg, add: Reg, dst: Reg },

    // I/O operations
    FRead(Reg),
    IRead(Reg),
    FWrite(Reg),
    IWrite(Reg),
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
    Frame { name: String, size: usize, params: Vec<String> },
    Global { name: String, size: usize, align: usize },
    String { name: String, content: String },
    Float { name: String, content: usize },
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

            // Pseudo operations
            [".data"] => instructions.push(Instruction::Data),
            [".text"] => instructions.push(Instruction::Text),
            [".frame", name, size, params @ ..] => {
                let params = if params.is_empty() {
                    vec![]
                } else {
                    params.iter().map(|s| s.to_string()).collect()
                };
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
            inst => todo!("{:?}", inst),
            // _ => {
            //     return Err("invalid instruction sequence");
            // }
        }
        println!("{:?}", instructions);
    }
    Ok(instructions)
}

#[test]
fn parse_iloc() {
    use std::fs;

    let text = fs::read_to_string("./input/check.il").unwrap();
    parse_text(&text).unwrap();
}
