use std::{
    cmp::Ordering,
    collections::{BTreeMap, BTreeSet, HashMap, VecDeque},
    default::default,
};

use crate::{
    iloc::{Block, IlocProgram, Instruction, Reg, Val},
    lcm::{print_maps, LoopAnalysis},
    ssa::{
        build_cfg,
        dce::{build_stripped_cfg, dead_code},
        dom_val_num, dominator_tree, find_loops, insert_phi_functions, reverse_postorder, OrdLabel,
    },
};

mod color;

use color::ColorNode;

pub const K_DEGREE: usize = 4;

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
    'func: for func in &mut prog.functions {
        let start = OrdLabel::new_start(&func.label);

        let cfg = build_cfg(func);
        let mut dtree = dominator_tree(&cfg, &mut func.blocks, &start);
        insert_phi_functions(func, &dtree.cfg_succs_map, &start, &dtree.dom_frontier_map);
        let mut meta = HashMap::new();
        let mut stack = VecDeque::new();
        dom_val_num(&mut func.blocks, 0, &mut meta, &dtree, &mut stack);

        // WARNING THIS IS EXPENSIVISH
        // Sneaky sneaky
        //
        // This removes dead phi nodes that otherwise complicate the interference graph
        dead_code(func, &dtree, &start);
        dtree.cfg_succs_map = build_stripped_cfg(func);

        let loop_map = find_loops(func, &dtree);

        let mut stack_size = func.stack_size;
        // TODO: Move/copy coalesce instructions in `build_interference`
        // TODO: Move/copy coalesce instructions in `build_interference`
        let (graph, interfere, defs) = loop {
            // This is the graph that goes with the following terminal printouts
            dump_to(&IlocProgram { preamble: vec![], functions: vec![func.clone()] });

            let (definitions, use_map) = color::build_use_def_map(&dtree, &start, &func.blocks);
            // TODO: make these Reg::Var to begin with...
            let mut defs: BTreeMap<_, BTreeSet<_>> = BTreeMap::new();
            for (d, locations) in definitions {
                for loc in locations {
                    defs.entry(d.to_register()).or_default().insert(loc);
                }
            }
            let mut uses: BTreeMap<_, BTreeSet<_>> = BTreeMap::new();
            for (d, locations) in use_map {
                for loc in locations {
                    uses.entry(d.to_register()).or_default().insert(loc);
                }
            }
            match color::build_interference(&func.blocks, &dtree, &start, &defs, &uses, &loop_map) {
                Ok((colored_graph, interfere)) => break (colored_graph, interfere, defs),
                Err(insert_spills) => {
                    println!("SPILLED {:?}", insert_spills);

                    let mut spills = vec![];
                    for blk in &func.blocks {
                        let mut count = 0;
                        for (i, inst) in blk.instructions.iter().enumerate() {
                            if let Some(dst) = inst.target_reg()
                                && insert_spills.contains(&dst.to_register())
                            {
                                stack_size += (4 * count);
                                count += 1;
                                for &(blk_idx, mut inst_idx) in defs.get(&dst.to_register()).unwrap_or(&BTreeSet::new()) {
                                    if inst_idx == 0 {
                                        match &func.blocks[blk_idx].instructions[0..2] {
                                            [Instruction::Frame {.. }, Instruction::Label(..)] => inst_idx += 2,
                                            [Instruction::Label(..), _] => inst_idx += 1,
                                            _ => {},
                                        }
                                    }
                                    spills.push(Spill::Store { stack_size, reg: *dst, blk_idx, inst_idx });
                                }
                                for &(blk_idx, mut inst_idx) in uses.get(&dst.to_register()).unwrap_or(&BTreeSet::new()) {
                                    if inst_idx == 0 {
                                        match &func.blocks[blk_idx].instructions[0..2] {
                                            [Instruction::Frame {.. }, Instruction::Label(..)] => inst_idx += 2,
                                            [Instruction::Label(..), _] => inst_idx += 1,
                                            _ => {},
                                        }
                                    }
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
                                // We don't need to store the phi again this was already
                                // taken care
                                // of on all paths above us
                                if matches!(
                                    &func.blocks[blk_idx].instructions[inst_idx],
                                    Instruction::Phi(..)
                                ) {
                                    continue;
                                }
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

                                let inst = &mut func.blocks[blk_idx].instructions;
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
                    std::io::stdin().read_line(&mut String::new());
                }
            }
        };
        func.stack_size = stack_size;

        return;

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

    println!("NUMBER OF REGS {}", K_DEGREE);
}

fn dump_to(prog: &IlocProgram) {
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
#[test]
fn ralloc_simple() {
    use std::fs;

    use crate::iloc::{make_basic_blocks, make_blks, parse_text};

    let input = "
    .data
    .text
.frame main, 0
    loadI 4 => %vr4
    loadI 42 => %vr42
    loadI 8 => %vr1
    add %vr1, %vr4 => %vr5
    mult %vr42, %vr4 => %vr7
    add %vr1, %vr7 => %vr7
    mult %vr5, %vr7 => %vr8
    add %vr4, %vr8 => %vr9
    ret
";
    let iloc = parse_text(input).unwrap();
    let mut blocks = make_basic_blocks(&make_blks(iloc));

    allocate_registers(&mut blocks);
    for f in &blocks.functions {
        for b in &f.blocks {
            for i in &b.instructions {
                print!("{}", i);
            }
        }
    }
}

fn emit_good_ralloc_viz(
    cfg: &HashMap<OrdLabel, BTreeSet<OrdLabel>>,
    start: &OrdLabel,
    blocks: &[Block],
    colored: &BTreeMap<Reg, ColorNode>,
    interfere: &BTreeMap<Reg, BTreeSet<Reg>>,
    definitions: &BTreeMap<Reg, Vec<(usize, usize)>>,
    file: &str,
) {
    use std::{
        collections::hash_map::DefaultHasher,
        fmt::Write,
        fs,
        hash::{Hash, Hasher},
    };
    fn str_id<T: Hash>(s: &T) -> u64 {
        let mut state = DefaultHasher::default();
        s.hash(&mut state);
        state.finish()
    }

    let mut defs: BTreeMap<_, BTreeSet<_>> = BTreeMap::new();
    for (d, locations) in definitions {
        for loc in locations {
            defs.entry(d.to_register()).or_default().insert(loc);
        }
    }
    let interfere_portion: usize = interfere.last_key_value().unwrap().0.as_usize();

    let mut seen_nodes = BTreeSet::new();
    let mut seen_edges = BTreeSet::new();
    let mut buf = String::new();
    writeln!(buf, "digraph cfg {{").unwrap();
    for n in reverse_postorder(cfg, start) {
        let blk_idx = blocks.iter().position(|b| b.label == n.as_str()).unwrap();
        let blk = &blocks[blk_idx];
        for (i_idx, inst) in blk.instructions.iter().enumerate() {
            if matches!(inst, Instruction::Skip(..) | Instruction::Phi(..)) {
                continue;
            }

            let mut wires = String::new();
            let mut rank = String::new();
            write!(rank, "{{rank=same; ");
            for reg in inst.registers_iter() {
                let reg = reg.to_register();

                let hue = (reg.as_usize() as f32) * (360.0 / interfere_portion as f32) / 360.0;

                if !seen_nodes.contains(&(reg, blk_idx, i_idx)) {
                    seen_nodes.insert((reg, blk_idx, i_idx));

                    writeln!(
                        buf,
                        "\"{}{}{}\" [label=\" {} {} \" shape=box color=\"{} 1 1\"]",
                        blk_idx,
                        i_idx,
                        str_id(&reg),
                        inst.inst_name(),
                        reg,
                        hue,
                    );
                    write!(rank, "\"{}{}{}\";", blk_idx, i_idx, str_id(&reg));
                }

                for live in interfere.get(&reg).unwrap_or(&BTreeSet::new()) {
                    for (bi, ii) in defs.get(&live.to_register()).unwrap_or(&BTreeSet::new()).iter()
                    // .filter(|(b, _)| *b == blk_idx)
                    {
                        if !seen_edges.contains(&(*live, reg)) {
                            seen_edges.insert((*live, reg));

                            writeln!(
                                wires,
                                "\"{}{}{}\" -> \"{}{}{}\" [color=\"{} 1 1\"]",
                                blk_idx,
                                i_idx,
                                str_id(&reg),
                                bi,
                                ii,
                                str_id(&live),
                                hue
                            );
                        }
                    }
                }
            }
            writeln!(rank, "}}");
            if !wires.is_empty() {
                buf.push_str(&rank);
                buf.push_str(&wires);
            }
        }
    }

    writeln!(buf, "}}").unwrap();
    fs::write(&format!("{}.dot", file), buf).unwrap();
}

fn emit_ralloc_viz(
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
    let interfere_len: usize = interfere.len();

    let mut buf = String::new();
    writeln!(buf, "digraph cfg {{").unwrap();
    for n in reverse_postorder(cfg, start) {
        let blk = blocks.iter().find(|b| b.label == n.as_str()).unwrap();
        writeln!(
            buf,
            "{} [shape = none, label = <\n<table border=\"0\" cellborder=\"1\" cellspacing=\"0\" cellpadding=\"4\">",
            blk.label.replace('.', "_")
        ).unwrap();

        writeln!(buf, "<tr><td>instruction</td><td colspan=\"3\">operands</td>");
        let mut last = 1;
        for reg in interfere.keys() {
            let s = reg.as_usize();
            for i in last..s - 1 {
                writeln!(buf, "<td>%vr{}</td>", i + 1);
            }
            last = s;
            writeln!(buf, "<td>{}</td>", reg);
        }
        writeln!(buf, "</tr>");

        let mut seen = BTreeSet::new();
        for inst in &blk.instructions {
            if matches!(inst, Instruction::Skip(..) | Instruction::Phi(..)) {
                continue;
            }

            let registers = inst.registers_iter();

            if !registers.is_empty() {
                writeln!(
                    buf,
                    "<tr><td>{}</td>",
                    inst.to_string().trim().replace('%', "").replace("=>", "=").replace("->", "-")
                );
                for _ in 0..(3 - registers.len()) {
                    writeln!(buf, "<td></td>");
                }

                let mut map = BTreeMap::<_, BTreeSet<_>>::new();
                for reg in &registers {
                    if matches!(reg, Reg::Phi(0, _)) {
                        writeln!(buf, "<td>sp</td>");
                        continue;
                    }
                    let reg = reg.to_register();
                    seen.insert(reg);

                    let hue = (reg.as_usize() as f32) * (360.0 / interfere_portion as f32) / 360.0;
                    writeln!(buf, "    <td bgcolor = \"{} 1 1\">{}</td>", hue, reg);

                    for node in interfere.get(&reg.to_register()).unwrap_or(&BTreeSet::new()) {
                        map.entry(*node).or_default().insert(reg);
                    }
                }
                let mut start = 0;
                for (live, because) in map {
                    if !seen.contains(&live) {
                        // continue;
                    }
                    let curr = live.as_usize();

                    for _ in start..curr - 1 {
                        writeln!(buf, "<td></td>");
                    }

                    let mut inner = String::new();
                    writeln!(inner, "<table><tr>");
                    for b in because {
                        let num = b.as_usize();
                        let hue = (num as f32) * (360.0 / interfere_portion as f32) / 360.0;
                        writeln!(inner, "    <td bgcolor = \"{} 1 1\">{}</td>", hue, b);
                    }
                    writeln!(inner, "</tr></table>");

                    let hue = (curr as f32) * (360.0 / interfere_portion as f32) / 360.0;
                    writeln!(buf, "    <td  bgcolor = \"{} 1 1\">{}</td>", hue, inner);
                    start = curr;
                }
                for _ in start..interfere_portion {
                    writeln!(buf, "<td></td>");
                }
                writeln!(buf, "</tr>");
            }
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
