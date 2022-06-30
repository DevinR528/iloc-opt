use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque},
    fmt,
    ops::{AddAssign, Range},
    process::Command,
};

use crate::{
    iloc::{Block, Function, Instruction, Operand, Reg},
    lcm::{print_maps, LoopAnalysis},
    sched::{HWResource, Hardware},
    ssa::{postorder, reverse_postorder, DominatorTree, OrdLabel},
};

use HWResource as HWR;

const READ: [HWR; 2] = [HWR::Read, HWR::Read];
const ADD: [HWR; 2] = [HWR::Arithmatic, HWR::Arithmatic];
const MULT: [HWR; 3] = [HWR::Multiplication, HWR::Multiplication, HWR::Multiplication];
const DIV: [HWR; 2] = [HWR::Division, HWR::Division];

/// An instruction's resource needs in order to finish.
pub struct InstResource(Vec<HWResource>);

impl InstResource {
    pub fn add() -> Self { Self([&READ as &[_], &ADD, &[HWR::Write]].concat()) }
    pub fn add_imm() -> Self {
        Self([&[HWR::Read] as &[_], &ADD, &[HWR::Write]].concat())
    }

    pub fn sub() -> Self { Self::add() }
    pub fn sub_imm() -> Self { Self::add_imm() }
    pub fn shift() -> Self { Self::add() }
    pub fn shift_imm() -> Self { Self::add_imm() }
    pub fn or() -> Self { Self::add() }
    pub fn and() -> Self { Self::add() }
    pub fn modu() -> Self { Self::add() }
    pub fn not() -> Self { Self::add() }

    pub fn mult() -> Self { Self([&READ as &[_], &MULT, &[HWR::Write]].concat()) }
    pub fn mult_imm() -> Self {
        Self([&[HWR::Read] as &[_], &MULT, &[HWR::Write]].concat())
    }

    pub fn div() -> Self { Self([&READ as &[_], &DIV, &[HWR::Write]].concat()) }

    pub fn mov() -> Self { Self(vec![HWR::Read]) }

    pub fn load() -> Self { Self(vec![HWR::Read]) }
    pub fn load_add() -> Self {
        Self([&READ as &[_], &ADD, &[HWR::Write, HWR::Read]].concat())
    }
    pub fn load_add_imm() -> Self {
        Self([&[HWR::Read] as &[_], &ADD, &[HWR::Write, HWR::Read]].concat())
    }

    pub fn store() -> Self { Self(vec![HWR::Read, HWR::Write]) }

    pub fn store_add() -> Self {
        Self([&READ as &[_], &ADD, &[HWR::Write, HWR::Read, HWR::Write]].concat())
    }

    pub fn store_add_imm() -> Self {
        Self([&[HWR::Read] as &[_], &ADD, &[HWR::Write, HWR::Read, HWR::Write]].concat())
    }

    pub fn cmp_br() -> Self {
        Self([&READ as &[_], &ADD, &[HWR::Read, HWR::Write]].concat())
    }
}

impl Instruction {
    /// Get the latency of this instruction. Latency is the measure of cycles an
    /// instruction takes to complete.
    fn latency(&self) -> u8 {
        match self {
            Self::Mult { .. } | Self::ImmMult { .. } | Self::Div { .. } => 3,
            Self::Load { .. }
            | Self::LoadAdd { .. }
            | Self::LoadAddImm { .. }
            | Self::Store { .. }
            | Self::StoreAdd { .. }
            | Self::StoreAddImm { .. } => 5,
            // All other instructions have a one cycle latency
            _ => 1,
        }
    }

    /// Get the resource table this instruction needs to execute.
    fn resource_table(&self) -> InstResource {
        match self {
            Self::I2I { .. } => InstResource::mov(),

            Self::Add { .. } => InstResource::add(),
            Self::ImmAdd { .. } => InstResource::add_imm(),
            Self::Sub { .. } => InstResource::sub(),
            Self::ImmSub { .. } => InstResource::sub_imm(),
            Self::And { .. } => InstResource::and(),
            Self::Or { .. } => InstResource::or(),
            Self::Not { .. } => InstResource::not(),
            Self::Mod { .. } => InstResource::modu(),

            Self::Div { .. } => InstResource::div(),

            Self::LShift { .. } | Self::ImmLShift { .. } => InstResource::shift(),
            Self::ImmLShift { .. } | Self::ImmRShift { .. } => InstResource::shift_imm(),

            Self::Mult { .. } => InstResource::mult(),
            Self::ImmMult { .. } => InstResource::mult_imm(),

            Self::Load { .. } => InstResource::load(),
            Self::LoadAdd { .. } => InstResource::load_add(),
            Self::LoadAddImm { .. } => InstResource::load_add_imm(),

            Self::Store { .. } => InstResource::store(),
            Self::StoreAdd { .. } => InstResource::store_add(),
            Self::StoreAddImm { .. } => InstResource::store_add_imm(),

            Self::CbrLT { .. }
            | Self::CbrLE { .. }
            | Self::CbrGT { .. }
            | Self::CbrGE { .. }
            | Self::CbrEQ { .. }
            | Self::CbrNE { .. } => InstResource::cmp_br(),

            Self::CbrLT { .. }
            | Self::CbrLE { .. }
            | Self::CbrGT { .. }
            | Self::CbrGE { .. }
            | Self::CbrEQ { .. }
            | Self::CbrNE { .. } => InstResource::add(),
            _ => todo!("more resource tables == {:?}", self),
        }
    }
}
