use std::{
    cmp::Ordering,
    collections::{BTreeMap, BTreeSet, HashMap, VecDeque},
    default::default,
};

use crate::{
    iloc::{Block, IlocProgram, Instruction, Reg, Val},
    lcm::LoopAnalysis,
    ssa::{
        build_cfg, dom_val_num, dominator_tree, find_loops, insert_phi_functions,
        reverse_postorder, OrdLabel,
    },
};

mod color;

use color::ColorNode;

pub const K_DEGREE: usize = 2;

#[derive(Debug)]
pub enum Spill {
    Store { stack_size: usize, reg: Reg, blk_idx: usize, inst_idx: usize },
    Load { stack_size: usize, reg: Reg, blk_idx: usize, inst_idx: usize },
}
impl Spill {
    pub fn blk_idx(&self) -> usize {
        match self {
            Self::Store { blk_idx, .. } => *blk_idx,
            Self::Load { blk_idx, .. } => *blk_idx,
        }
    }
    pub fn inst_idx(&self) -> usize {
        match self {
            Self::Store { inst_idx, .. } => *inst_idx,
            Self::Load { inst_idx, .. } => *inst_idx,
        }
    }
}

pub fn allocate_registers(prog: &mut IlocProgram) {
    return;
    'func: for func in &mut prog.functions {
        let start = OrdLabel::new_start(&func.label);

        let cfg = build_cfg(func);
        let dtree = dominator_tree(&cfg, &mut func.blocks, &start);
        insert_phi_functions(func, &dtree.cfg_succs_map, &start, &dtree.dom_frontier_map);
        let mut meta = HashMap::new();
        let mut stack = VecDeque::new();
        dom_val_num(&mut func.blocks, 0, &mut meta, &dtree, &mut stack);

        let loop_map = find_loops(func, &dtree);

        let mut stack_size = func.stack_size;
        // TODO: Move/copy coalesce instructions in `build_interference`
        // TODO: Move/copy coalesce instructions in `build_interference`
        let (graph, interfere) = loop {
            let (defs, uses) = color::build_use_def_map(&dtree, &start, &func.blocks);
            match color::build_interference(&func.blocks, &dtree, &start, &defs, &uses, &loop_map) {
                Ok((colored_graph, interfere)) => break (colored_graph, interfere),
                Err((mut last_reg, insert_spills)) => {
                    println!("{:?}", insert_spills);

                    let mut spills = vec![];
                    for blk in &mut func.blocks {
                        let mut count = 0;
                        for (i, inst) in blk.instructions.iter_mut().enumerate() {
                            if let Some(dst) = inst.target_reg()
                                && insert_spills.contains(&dst.to_register())
                            {
                                stack_size += (4 * count);
                                count += 1;
                                for &(blk_idx, inst_idx) in defs.get(dst).unwrap_or(&vec![]) {
                                    spills.push(Spill::Store { stack_size, reg: *dst, blk_idx, inst_idx });
                                }
                                for &(blk_idx, inst_idx) in uses.get(dst).unwrap_or(&vec![]) {
                                    spills.push(Spill::Load { stack_size, reg: *dst, blk_idx, inst_idx });
                                }
                            }
                        }
                    }

                    spills.sort_by(|a, b| match a.blk_idx().cmp(&b.blk_idx()) {
                        Ordering::Equal => a.inst_idx().cmp(&b.inst_idx()),
                        res => res,
                    });

                    let mut curr_blk_idx = 0;
                    let mut add = 0;
                    for spill in spills {
                        match spill {
                            Spill::Store { stack_size, reg, blk_idx, inst_idx } => {
                                if blk_idx != curr_blk_idx {
                                    curr_blk_idx = blk_idx;
                                    add = 0;
                                }
                                func.blocks[blk_idx].instructions.insert(
                                    inst_idx + add + 1,
                                    Instruction::StoreAddImm {
                                        src: reg,
                                        add: Val::Integer(-(stack_size as isize)),
                                        dst: Reg::Phi(0, 0),
                                    },
                                );
                                if blk_idx == curr_blk_idx {
                                    add += 1;
                                }
                            }
                            Spill::Load { stack_size, reg, blk_idx, inst_idx } => {
                                if blk_idx != curr_blk_idx {
                                    curr_blk_idx = blk_idx;
                                    add = 0;
                                }
                                // let Reg::Var(r) = last_reg else { unreachable!() };
                                // last_reg = Reg::Var(r + 1);
                                let inst = &mut func.blocks[blk_idx].instructions;
                                // Make sure the use respects the new register number

                                // match inst[inst_idx + add].operands_mut() {
                                //     (Some(a), _) if *a == reg => {
                                //         *a = last_reg;
                                //     }
                                //     (_, Some(b)) if *b == reg => {
                                //         *b = last_reg;
                                //     }
                                //     // Any other register used in the instruction (DUH)
                                //     _ => {}
                                // }
                                inst.insert(
                                    (inst_idx + add),
                                    Instruction::LoadAddImm {
                                        src: Reg::Phi(0, 0),
                                        add: Val::Integer(-(stack_size as isize)),
                                        dst: reg,
                                    },
                                );
                                if blk_idx == curr_blk_idx {
                                    add += 1;
                                }
                            }
                        }
                    }
                }
            }
        };
        func.stack_size = stack_size;

        // emit_cfg_viz(&dtree.cfg_succs_map, &start, &func.blocks, &graph, &interfere, "pre2");

        for blk in &mut func.blocks {
            for inst in &mut blk.instructions {
                for reg in inst.registers_mut_iter() {
                    if matches!(reg, Reg::Phi(0, _)) {
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

fn emit_cfg_viz(
    cfg: &HashMap<OrdLabel, BTreeSet<OrdLabel>>,
    start: &OrdLabel,
    blocks: &[Block],
    colored: &BTreeMap<Reg, ColorNode>,
    interfere: &BTreeMap<Reg, BTreeSet<Reg>>,
    file: &str,
) {
    use std::{
        collections::hash_map::DefaultHasher,
        fmt::Write,
        fs,
        hash::{Hash, Hasher},
    };

    fn str_id(s: &Reg) -> u64 {
        let mut state = DefaultHasher::default();
        s.hash(&mut state);
        state.finish()
    }

    let interfere_portion: usize = interfere.last_key_value().unwrap().0.as_usize();

    let mut buf = String::new();
    writeln!(buf, "digraph cfg {{").unwrap();
    for n in reverse_postorder(cfg, start) {
        let blk = blocks.iter().find(|b| b.label == n.as_str()).unwrap();
        writeln!(
            buf,
            "{} [shape = none, label = <\n<table border=\"0\" cellborder=\"1\" cellspacing=\"0\" cellpadding=\"4\">",
            blk.label.replace('.', "_")
        ).unwrap();

        for inst in &blk.instructions {
            if matches!(inst, Instruction::Skip(..) | Instruction::Phi(..)) {
                continue;
            }
            writeln!(
                buf,
                "  <tr>\n    <td>{}</td>",
                inst.to_string().trim().replace('%', "").replace("=>", "=").replace("->", "-")
            );

            let mut fill = 0;
            for reg in inst.registers_iter() {
                fill += 1;
                if matches!(reg, Reg::Phi(0, _)) {
                    writeln!(buf, "    <td>sp</td>");
                    continue;
                }

                let node = colored.get(&reg.to_register()).unwrap_or_else(|| panic!("{:?}", reg));
                let hue = (*node.color.int() as f32) * (360.0 / K_DEGREE as f32) / 360.0;
                writeln!(buf, "    <td bgcolor = \"{} 1 1\">{}</td>", hue, node.color.int());
            }
            for _ in fill..3 {
                writeln!(buf, "    <td>e</td>");
            }

            let mut reg_to_interfering: BTreeMap<_, BTreeSet<_>> = BTreeMap::new();
            for reg in inst.registers_iter() {
                if matches!(reg, Reg::Phi(0, _)) {
                    writeln!(buf, "    <td>sp</td>");
                    continue;
                }
                let sets = reg_to_interfering.entry(reg.to_register()).or_default();
                *sets = sets
                    .union(interfere.get(&reg.to_register()).unwrap_or(&BTreeSet::new()))
                    .copied()
                    .collect();
            }

            let slice: Vec<_> = reg_to_interfering.into_iter().collect();
            match slice.as_slice() {
                [(r, set)] => {
                    let from_hue =
                        (r.as_usize() as f32) * (360.0 / interfere_portion as f32) / 360.0;

                    for n in set {
                        let hue =
                            (n.as_usize() as f32) * (360.0 / interfere_portion as f32) / 360.0;
                        writeln!(
                            buf,
                            "    <td><table><tr><td bgcolor = \"{} 1 1\">{}</td><td bgcolor=\"{} 0.3 1\">{}</td></tr></table></td>",
                            hue,
                            n.as_usize(),
                            from_hue,
                            r.as_usize()
                        );
                    }
                }
                [(r_1, set_1), (r_2, set_2)] => {
                    let from_hue_1 =
                        (r_1.as_usize() as f32) * (360.0 / interfere_portion as f32) / 360.0;
                    let from_hue_2 =
                        (r_2.as_usize() as f32) * (360.0 / interfere_portion as f32) / 360.0;
                    // Common
                    for n in set_1.intersection(set_2) {
                        let hue =
                            (n.as_usize() as f32) * (360.0 / interfere_portion as f32) / 360.0;
                        writeln!(
                            buf,
                            "    <td><table><tr><td bgcolor = \"{} 1 1\">{}</td><td bgcolor=\"{} 0.3 1\">{}</td><td bgcolor=\"{} 0.3 1\">{}</td></tr></table></td>",
                            hue,
                            n.as_usize(),
                            from_hue_1,
                            r_1.as_usize(),
                            from_hue_2,
                            r_2.as_usize(),
                        );
                    }
                    // Only for set_1
                    for n in set_1.difference(set_2) {
                        let hue =
                            (n.as_usize() as f32) * (360.0 / interfere_portion as f32) / 360.0;
                        writeln!(
                            buf,
                            "    <td><table><tr><td bgcolor = \"{} 1 1\">{}</td><td bgcolor=\"{} 0.3 1\">{}</td></tr></table></td>",
                            hue,
                            n.as_usize(),
                            from_hue_1,
                            r_1.as_usize(),
                        );
                    }
                    // Only set_2
                    for n in set_2.difference(set_1) {
                        let hue =
                            (n.as_usize() as f32) * (360.0 / interfere_portion as f32) / 360.0;
                        writeln!(
                            buf,
                            "    <td><table><tr><td bgcolor = \"{} 1 1\">{}</td><td bgcolor=\"{} 0.3 1\">{}</td></tr></table></td>",
                            hue,
                            n.as_usize(),
                            from_hue_2,
                            r_2.as_usize(),
                        );
                    }
                }
                [(r_1, set_1), (r_2, set_2), (r_3, set_3)] => {
                    let from_hue_1 =
                        (r_1.as_usize() as f32) * (360.0 / interfere_portion as f32) / 360.0;
                    let from_hue_2 =
                        (r_2.as_usize() as f32) * (360.0 / interfere_portion as f32) / 360.0;
                    let from_hue_3 =
                        (r_3.as_usize() as f32) * (360.0 / interfere_portion as f32) / 360.0;
                    // Common to all
                    for n in set_1
                        .intersection(set_2)
                        .cloned()
                        .collect::<BTreeSet<_>>()
                        .intersection(set_3)
                    {
                        let hue =
                            (n.as_usize() as f32) * (360.0 / interfere_portion as f32) / 360.0;
                        writeln!(
                            buf,
                            "    <td><table><tr><td bgcolor = \"{} 1 1\">{}</td><td bgcolor=\"{} 0.3 1\">{}</td><td bgcolor=\"{} 0.3 1\">{}</td><td bgcolor=\"{} 0.3 1\">{}</td></tr></table></td>",
                            hue,
                            n.as_usize(),
                            from_hue_1,
                            r_1.as_usize(),
                            from_hue_2,
                            r_2.as_usize(),
                            from_hue_3,
                            r_3.as_usize(),
                        );
                    }
                    // Common to 1 and 2
                    for n in set_1.intersection(set_2) {
                        let hue =
                            (n.as_usize() as f32) * (360.0 / interfere_portion as f32) / 360.0;
                        writeln!(
                            buf,
                            "    <td><table><tr><td bgcolor = \"{} 1 1\">{}</td><td bgcolor=\"{} 0.3 1\">{}</td><td bgcolor=\"{} 0.3 1\">{}</td></tr></table></td>",
                            hue,
                            n.as_usize(),
                            from_hue_1,
                            r_1.as_usize(),
                            from_hue_2,
                            r_2.as_usize(),
                        );
                    }
                    // Common to 2 and 3
                    for n in set_2.intersection(set_3) {
                        let hue =
                            (n.as_usize() as f32) * (360.0 / interfere_portion as f32) / 360.0;
                        writeln!(
                            buf,
                            "    <td><table><tr><td bgcolor = \"{} 1 1\">{}</td><td bgcolor=\"{} 0.3 1\">{}</td><td bgcolor=\"{} 0.3 1\">{}</td></tr></table></td>",
                            hue,
                            n.as_usize(),
                            from_hue_2,
                            r_1.as_usize(),
                            from_hue_3,
                            r_2.as_usize(),
                        );
                    }
                    // Common to 1 and 3
                    for n in set_1.intersection(set_3) {
                        let hue =
                            (n.as_usize() as f32) * (360.0 / interfere_portion as f32) / 360.0;
                        writeln!(
                            buf,
                            "    <td><table><tr><td bgcolor = \"{} 1 1\">{}</td><td bgcolor=\"{} 0.3 1\">{}</td><td bgcolor=\"{} 0.3 1\">{}</td></tr></table></td>",
                            hue,
                            n.as_usize(),
                            from_hue_1,
                            r_1.as_usize(),
                            from_hue_3,
                            r_2.as_usize(),
                        );
                    }
                    // Only for set_1
                    for n in set_1.difference(&set_2.union(set_3).copied().collect()) {
                        let hue =
                            (n.as_usize() as f32) * (360.0 / interfere_portion as f32) / 360.0;
                        writeln!(
                            buf,
                            "<td><table><tr><td bgcolor = \"{} 1 1\">{}</td><td bgcolor=\"{} 0.3 1\">{}</td></tr></table></td>",
                            hue,
                            n.as_usize(),
                            from_hue_1,
                            r_1.as_usize(),
                        );
                    }
                    // Only set_2
                    for n in set_2.difference(&set_1.union(set_3).copied().collect()) {
                        let hue =
                            (n.as_usize() as f32) * (360.0 / interfere_portion as f32) / 360.0;
                        writeln!(
                            buf,
                            "<td><table><tr><td bgcolor = \"{} 1 1\">{}</td><td bgcolor=\"{} 0.3 1\">{}</td></tr></table></td>",
                            hue,
                            n.as_usize(),
                            from_hue_2,
                            r_2.as_usize(),
                        );
                    }
                    // Only set_3
                    for n in set_3.difference(&set_1.union(set_2).copied().collect()) {
                        let hue =
                            (n.as_usize() as f32) * (360.0 / interfere_portion as f32) / 360.0;
                        writeln!(
                            buf,
                            "<td><table><tr><td bgcolor = \"{} 1 1\">{}</td><td bgcolor=\"{} 0.3 1\">{}</td></tr></table></td>",
                            hue,
                            n.as_usize(),
                            from_hue_2,
                            r_2.as_usize(),
                        );
                    }
                }
                [] | [..] => {}
            }

            writeln!(buf, "  </tr>");
        }
        writeln!(buf, "</table>>]");

        for e in cfg.get(n).unwrap_or(&BTreeSet::new()) {
            writeln!(buf, "{} -> {}", n.as_str().replace('.', "_"), e.as_str().replace('.', "_"))
                .unwrap();
        }
    }

    writeln!(buf, "}}").unwrap();
    fs::write(&format!("{}.dot", file), buf).unwrap();
}
