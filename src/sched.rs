use std::{
    borrow::Borrow,
    cmp::Ordering,
    collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque},
    hash::{Hash, Hasher},
    mem::discriminant,
    process::Command,
};

use crate::{
    iloc::{Block, Function, IlocProgram, Instruction, Reg, Val},
    lcm::{find_loops, print_maps, print_maps_display, LoopAnalysis},
    ralloc::allocate_registers,
    ssa::{dom_val_num, insert_phi_functions, DominatorTree, OrdLabel},
};

mod inst;
mod swing;

#[derive(Clone, Copy, Debug)]
/// A hardware resource, each represent a unit of hardware that is required for the
/// instruction to complete.
pub enum HWResource {
    /// A unit of work done by the adder.
    Arithmatic,
    /// A unit of work done by the multiply hardware.
    Multiplication,
    /// A unit of work done by the divider.
    Division,
    /// A unit of work done by the load/reader.
    Read,
    /// A unit of work done by the store/writer.
    Write,
}

/// This is our default test resource table.
///
/// | add 0 | add 1 | mult 0 | mult 1 | mult 2 | load 0 | load 1 | store 0|
/// |-------|-------|--------|--------|--------|--------|--------|--------|
/// |       |       |        |        |        |        |        |        |
/// |-------|-------|--------|--------|--------|--------|--------|--------|
/// |       |       |        |        |        |        |        |        |
/// |-------|-------|--------|--------|--------|--------|--------|--------|
/// |       |       |        |        |        |        |        |        |
/// |-------|-------|--------|--------|--------|--------|--------|--------|
pub static RESOURCES: Hardware =
    Hardware { adder_units: 2, mult_unit: 3, div_unit: 0, load_units: 2, store_units: 2 };

pub struct Hardware {
    /// Number of hardware units that processes additions.
    pub adder_units: u8,
    /// Number of hardware units that can multiply.
    pub mult_unit: u8,
    /// Number of hardware units that can divide.
    pub div_unit: u8,
    /// Number of hardware units that can load.
    pub load_units: u8,
    /// Number of hardware units that can store.
    pub store_units: u8,
}

fn compute_init_interval(ddg: &DDGraph, func: &Function) -> u32 { 5 }

#[derive(Debug)]
pub enum DDKind {
    True(Instruction),
    Anti(Instruction),
    Output(Instruction),
}

#[derive(Debug, Default)]
pub struct DDGraph {
    pub roots: HashMap<Instruction, Vec<DDKind>>,
}

impl DDGraph {
    fn new(func: &Function, loop_info: &LoopAnalysis) -> Self {
        let mut ddg = DDGraph::default();

        for blk in &func.blocks {
            if loop_info.level_of_nesting(&OrdLabel::new(&blk.label)) > 0 {
                let mut read = BTreeMap::new();
                let mut written = BTreeMap::<_, &Instruction>::new();

                for (i, inst) in blk.instructions.iter().enumerate() {
                    if matches!(inst, Instruction::Skip(..)) {
                        continue;
                    }
                    print!("{inst}");
                    // TODO:
                    //
                    // - Check if the instruction is loop invariant
                    //   - if all operands are (they are NOT live-in to the loop)
                    // - Check is affine
                    // - Determine the dependence number
                    //   - is this live-out across the loop
                    for reg in inst.operand_iter() {
                        // True dependence
                        if let Some(&dep_inst) = written.get(&reg) {
                            ddg.roots
                                // The first instruction writes
                                .entry(dep_inst.clone())
                                .or_insert_with(Vec::new)
                                // The second instruction reads
                                .push(DDKind::True(inst.clone()));
                        }
                        read.insert(reg, inst);
                    }
                    if let Some(reg) = inst.target_reg() {
                        // Anti dependence
                        if let Some(&dep_inst) = read.get(reg) {
                            ddg.roots
                                // The first instruction reads
                                .entry(dep_inst.clone())
                                .or_insert_with(Vec::new)
                                // The second writes
                                .push(DDKind::Anti(inst.clone()));
                        }
                        // The set already contains this element
                        // we have an output dependence
                        if let Some(dep_inst) = written.insert(*reg, inst) {
                            ddg.roots
                                .entry(dep_inst.clone())
                                .or_insert_with(Vec::new)
                                .push(DDKind::Output(inst.clone()));
                        }
                    }
                }

                let init_interval = compute_init_interval(&ddg, func);
            }
        }

        print_maps_display("data dep", ddg.roots.iter());

        ddg
    }
}

pub fn schedual_prog(func: &mut Function, domtree: &DominatorTree) {
    insert_phi_functions(func, &domtree.cfg_succs_map, &domtree.dom_frontier_map);
    let mut meta = HashMap::new();
    let mut stack = VecDeque::new();
    dom_val_num(&mut func.blocks, 0, &mut meta, domtree, &mut stack);
    let loops = find_loops(domtree);

    DDGraph::new(func, &loops);

    print_maps("loops", loops.loop_map().iter());
    panic!()
}
