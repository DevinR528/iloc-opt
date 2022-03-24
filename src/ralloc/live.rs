use std::{
    collections::{BTreeSet, HashMap, VecDeque},
    ops::Range,
};

use crate::{
    iloc::{Block, Instruction, Operand, Reg},
    ssa::DominatorTree,
};
