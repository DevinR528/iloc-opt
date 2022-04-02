use std::collections::{HashMap, VecDeque};

use crate::{
    iloc::{IlocProgram, Instruction, Reg},
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
        let graph = loop {
            let (defs, uses) = live::build_use_def_map(&dtree, &start, &func.blocks);
            match live::build_ranges(
                &func.blocks,
                &dtree,
                cfg.exits.first().unwrap(),
                &start,
                &defs,
                &uses,
                &loop_map,
            ) {
                Ok(colored_graph) => break colored_graph,
                Err(insert_spills) => {
                    println!("{:?}", insert_spills);
                    for blk in &mut func.blocks {
                        for inst in &mut blk.instructions {
                            if let Some(dst) = inst.target_reg() && insert_spills.contains(&dst.to_register()) {
                                panic!("SPILL ME NOOOOO {:?}", dst)
                            }
                        }
                    }
                }
            }
        };

        for blk in &mut func.blocks {
            for inst in &mut blk.instructions {
                for reg in inst.registers_mut_iter() {
                    if *reg == Reg::Phi(0, 0) {
                        *reg = Reg::Var(0);
                        continue;
                    }

                    let node = graph.get(&reg.to_register()).unwrap_or_else(|| panic!("{:?}", reg));
                    *reg = Reg::Var((*node.color.int()) as usize);
                }
            }
        }
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
