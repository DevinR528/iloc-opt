use std::collections::{HashMap, VecDeque};

use crate::{
    iloc::{IlocProgram, Instruction},
    lcm::LoopAnalysis,
    ssa::{build_cfg, dom_val_num, dominator_tree, find_loops, insert_phi_functions, OrdLabel},
};

mod color;
mod live;

pub fn allocate_registers(prog: &mut IlocProgram) {
    for func in &mut prog.functions {
        let start = OrdLabel::new_start(&func.label);

        let cfg = build_cfg(func);
        let dtree = dominator_tree(&cfg, &mut func.blocks, &start);
        insert_phi_functions(func, &dtree.cfg_succs_map, &start, &dtree.dom_frontier_map);
        let mut meta = HashMap::new();
        let mut stack = VecDeque::new();
        dom_val_num(&mut func.blocks, 0, &mut meta, &dtree, &mut stack);

        let loop_map = find_loops(func, &dtree);
        // TODO: safe to move instructions around here for better live ranges??
        let ranges =
            live::build_ranges(&func.blocks, &dtree, cfg.exits.first().unwrap(), &start, &loop_map);
    }

    let mut buf = String::new();
    let x: bool;
    unsafe {
        x = crate::SSA;
        crate::SSA = true;
    }
    for inst in prog.functions.iter().flat_map(|f| f.flatten_block_iter()) {
        if matches!(inst, Instruction::Skip(..)) {
            continue;
        }
        buf.push_str(&inst.to_string())
    }
    unsafe {
        crate::SSA = x;
    }

    let mut path = std::path::PathBuf::from("./input/ralloc.il");
    let file = path.file_stem().unwrap().to_string_lossy().to_string();
    path.set_file_name(&format!("{}.pre.ssa.il", file));
    let mut fd =
        std::fs::OpenOptions::new().create(true).truncate(true).write(true).open(&path).unwrap();
    // Call the trait so I don't import stuff that will just be deleted
    std::io::Write::write_all(&mut fd, buf.as_bytes()).unwrap();
}
