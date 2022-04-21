use std::{
    cmp::Ordering,
    collections::{BTreeMap, BTreeSet, HashMap, VecDeque, HashSet},
    default::default, borrow::Borrow,
};

use crate::{
    iloc::{Block, IlocProgram, Instruction, Reg, Val},
    lcm::{print_maps, LoopAnalysis},
    ralloc::color::{ColoredGraph, FailedColoring},
    ssa::{
        build_cfg,
        dce::{build_stripped_cfg, dead_code},
        dom_val_num, dominator_tree, find_loops, insert_phi_functions, reverse_postorder, OrdLabel,
    },
};

mod color;

use color::ColorNode;

pub const K_DEGREE: usize = 8;

#[derive(Debug, Hash)]
pub enum Spill {
    Store { stack_size: usize, reg: Reg, blk_idx: usize, inst_idx: usize },
    Load { stack_size: usize, reg: Reg, blk_idx: usize, inst_idx: usize },
    ImmLoad { src: Val, reg: Reg, blk_idx: usize, inst_idx: usize },
    Remove { blk_idx: usize, inst_idx: usize },
}
impl PartialEq for Spill {
    fn eq(&self, other: &Self) -> bool {
        self.blk_idx() == other.blk_idx() && self.inst_idx() == other.inst_idx()
    }
}
impl Eq for Spill {}
impl PartialOrd for Spill {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(match self.blk_idx().cmp(&other.blk_idx()) {
            Ordering::Equal => self.inst_idx().cmp(&other.inst_idx()),
            res => res,
        })
    }
}
impl Ord for Spill {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.blk_idx().cmp(&other.blk_idx()) {
            Ordering::Equal => self.inst_idx().cmp(&other.inst_idx()),
            res => res,
        }
    }
}
impl Spill {
    pub fn blk_idx(&self) -> usize {
        match self {
            Self::Store { blk_idx, .. } => *blk_idx,
            Self::Load { blk_idx, .. } => *blk_idx,
            Self::ImmLoad { blk_idx, .. } => *blk_idx,
            Self::Remove { blk_idx, .. } => *blk_idx,
        }
    }
    pub fn inst_idx(&self) -> usize {
        match self {
            Self::Store { inst_idx, .. } => *inst_idx,
            Self::Load { inst_idx, .. } => *inst_idx,
            Self::ImmLoad { inst_idx, .. } => *inst_idx,
            Self::Remove { inst_idx, .. } => *inst_idx,
        }
    }
}

pub fn allocate_registers(prog: &mut IlocProgram) {
    'func: for func in &mut prog.functions {
        let start = OrdLabel::entry();
        let exit = OrdLabel::exit();

        // Don't double the number of entry and exit blocks added, caused entry and
        // exit to become loops (now that we compute self loops in `loop_info::find_loops`)
        func.blocks.retain(|blk| blk.label != ".E_exit" && blk.label != ".E_entry");

        let cfg = build_cfg(func);
        let mut dtree = dominator_tree(&cfg, &mut func.blocks);
        insert_phi_functions(func, &dtree.cfg_succs_map, &dtree.dom_frontier_map);
        let mut meta = HashMap::new();
        let mut stack = VecDeque::new();
        dom_val_num(&mut func.blocks, 0, &mut meta, &dtree, &mut stack);

        // WARNING THIS IS EXPENSIVE-ISH
        // Sneaky sneaky
        //
        // This removes dead phi nodes that otherwise complicate the interference graph,
        // also cleans up code motion blocks that could just be fallthrough
        dead_code(func, &dtree, &start);
        // We now have to clean up the cfg graph... YET AGAIN
        dtree.cfg_succs_map = build_stripped_cfg(func);
        dtree.cfg_preds_map.clear();
        for (from, set) in &dtree.cfg_succs_map {
            for to in set {
                dtree.cfg_preds_map.entry(to.clone()).or_default().insert(from.clone());
            }
        }

        let loop_map = find_loops(func, &dtree);

        let mut stack_size = func.stack_size;
        // TODO: Move/copy coalesce instructions in `build_interference`
        // TODO: Move/copy coalesce instructions in `build_interference`
        let (graph, interfere, defs) = loop {
            match color::build_interference(&mut func.blocks, &dtree, &loop_map) {
                Ok(ColoredGraph { graph, interference, defs }) => {
                    break (graph, interference, defs)
                }
                Err(FailedColoring { insert_spills, uses, defs }) => {
                    println!("SPILLED {:?}", insert_spills);

                    let mut spills = HashSet::new();
                    for (b, blk) in func.blocks.iter().enumerate() {
                        let mut count = 1;
                        for (i, inst) in blk.instructions.iter().enumerate() {
                            // Rematerialize loadI's (this is an easy no work win)
                            if let Instruction::ImmLoad { src, dst } = inst
                                && insert_spills.contains(dst)
                            {
                                spills.insert(Spill::Remove { blk_idx: b, inst_idx: i });
                                for &(blk_idx, mut inst_idx) in uses.get(dst).unwrap_or(&BTreeSet::new()) {
                                    if inst_idx == 0 {
                                        match &func.blocks[blk_idx].instructions[0..2] {
                                            [Instruction::Frame {.. }, Instruction::Label(..)] => inst_idx += 2,
                                            [Instruction::Label(..), _] => inst_idx += 1,
                                            _ => {},
                                        }
                                    }
                                    spills.insert(Spill::ImmLoad { src: src.clone(), reg: *dst, blk_idx, inst_idx });
                                }
                            } else if let Instruction::Frame { params, .. } = inst
                                && params.iter().any(|p| insert_spills.contains(p))
                            {
                                for param in params.iter().filter(|p| insert_spills.contains(p)) {
                                    for &(blk_idx, mut inst_idx) in defs.get(param).unwrap_or(&BTreeSet::new()) {
                                        if inst_idx == 0 {
                                            if let [Instruction::Frame {.. }, Instruction::Label(..)] = &func.blocks[blk_idx].instructions[0..2] {
                                                inst_idx += 1;
                                            }
                                        }

                                        spills.insert(Spill::Store { stack_size, reg: *param, blk_idx, inst_idx });
                                    }
                                    for &(blk_idx, mut inst_idx) in uses.get(param).unwrap_or(&BTreeSet::new()) {
                                        if inst_idx == 0 {
                                            if let [Instruction::Frame {.. }, Instruction::Label(..)] = &func.blocks[blk_idx].instructions[0..2] {
                                                inst_idx += 1;
                                            }
                                        }
                                        spills.insert(Spill::Load { stack_size, reg: *param, blk_idx, inst_idx });
                                    }
                                    stack_size += (4 * count);
                                    count += 1;
                                }
                            } else if let Some(dst) = inst.target_reg()
                                && insert_spills.contains(dst)
                            {
                                for &(blk_idx, mut inst_idx) in defs.get(dst).unwrap_or(&BTreeSet::new()) {
                                    if inst_idx == 0 {
                                        if let [Instruction::Frame {.. }, Instruction::Label(..)] = &func.blocks[blk_idx].instructions[0..2] {
                                            inst_idx += 1;
                                        }
                                    }
                                    spills.insert(Spill::Store { stack_size, reg: *dst, blk_idx, inst_idx });
                                }
                                for &(blk_idx, mut inst_idx) in uses.get(dst).unwrap_or(&BTreeSet::new()) {
                                    if inst_idx == 0 {
                                        if let [Instruction::Frame {.. }, Instruction::Label(..)] = &func.blocks[blk_idx].instructions[0..2] {
                                            inst_idx += 1;
                                        }
                                    }
                                    spills.insert(Spill::Load { stack_size, reg: *dst, blk_idx, inst_idx });
                                }

                                stack_size += (4 * count);
                                count += 1;
                            }
                        }
                    }

                    let mut spills = spills.into_iter().collect::<Vec<_>>();
                    spills.sort();

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
                                add += 1;
                            }
                            Spill::Load { stack_size, reg, blk_idx, inst_idx } => {
                                if blk_idx != curr_blk_idx {
                                    curr_blk_idx = blk_idx;
                                    add = 0;
                                }

                                func.blocks[blk_idx].instructions.insert(
                                    (inst_idx + add),
                                    Instruction::LoadAddImm {
                                        src: Reg::Phi(0, 0),
                                        add: Val::Integer(-(stack_size as isize)),
                                        dst: reg,
                                    },
                                );
                                add += 1;
                            }
                            // Rematerialize instead of load/store
                            Spill::ImmLoad { src, reg, blk_idx, inst_idx } => {
                                if blk_idx != curr_blk_idx {
                                    curr_blk_idx = blk_idx;
                                    add = 0;
                                }

                                func.blocks[blk_idx].instructions.insert(
                                    (inst_idx + add),
                                    Instruction::ImmLoad { src, dst: reg },
                                );
                                add += 1;
                            }
                            Spill::Remove { blk_idx, inst_idx } => {
                                func.blocks[blk_idx].instructions[inst_idx + add] =
                                    Instruction::Skip(format!(
                                        "[rematerial] {}",
                                        func.blocks[blk_idx].instructions[inst_idx + add]
                                    ));
                            }
                        }
                    }

                    // We need to keep up with all the variables on the stack
                    //
                    // Was doing this outside th loop but that won't keep track of were
                    // we are if we need to spill 2 times
                    func.stack_size = stack_size;

                    dump_to(
                        &IlocProgram { preamble: vec![], functions: vec![func.clone()] },
                        &format!("{}ra", func.label),
                    );
                }
            }
        };

        for blk in &mut func.blocks {
            for inst in &mut blk.instructions {
                for reg in inst.registers_mut_iter() {
                    // There should never be a phi left, just in case...
                    if matches!(reg, Reg::Var(0) | Reg::Phi(0, _)) {
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

static mut CNT: usize = 0;
fn dump_to(prog: &IlocProgram, name: &str) {
    let mut buf = String::new();
    let x: bool;
    let cnt: usize;
    unsafe {
        CNT += 1;
        cnt = CNT;

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

    let mut path = std::path::PathBuf::from(&format!("./input/{}.il", name));
    let file = path.file_stem().unwrap().to_string_lossy().to_string();
    path.set_file_name(&format!("{}{}.ralloc.il", file, cnt));
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

fn emit_ralloc_viz(
    cfg_succs: &HashMap<OrdLabel, BTreeSet<OrdLabel>>,
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
    for block in reverse_postorder(cfg_succs, start) {
        let blk = blocks.iter().find(|b| b.label == block.as_str()).unwrap();
        writeln!(
            buf,
            "{} [shape = none, label = <\n<table border=\"0\" cellborder=\"1\" cellspacing=\"0\" cellpadding=\"4\">",
            blk.label.replace('.', "_")
        ).unwrap();

        writeln!(buf, "<tr><td>{block}</td><td colspan=\"3\">operands</td>");
        let mut last = 1;
        for reg in interfere.keys() {
            let s = reg.as_usize();
            for i in last..s - 1 {
                writeln!(buf, "<td colspan=\"3\">%vr{}</td>", i + 1);
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
                    // only start coloring when we actually have defined the register
                    if !seen.contains(&live) {
                        continue;
                    }
                    let curr = live.as_usize();

                    // All the blocks before `curr` that are empty
                    for _ in start..curr - 1 {
                        writeln!(buf, "<td></td>");
                    }

                    // The registers that are used in the instruction and mark who interferes with
                    // them
                    let mut inner = String::new();
                    writeln!(inner, "<table><tr colspan = \"3\">");
                    for b in &because {
                        let num = b.as_usize();
                        let hue = (num as f32) * (360.0 / interfere_portion as f32) / 360.0;
                        writeln!(inner, "    <td bgcolor = \"{} 1 1\">{}</td>", hue, b);
                    }
                    for _ in 0..(3 - because.len()) {
                        writeln!(inner, "<td></td>");
                    }
                    writeln!(inner, "</tr></table>");

                    // Background (the register that is interfering)
                    let hue = (curr as f32) * (360.0 / interfere_portion as f32) / 360.0;
                    writeln!(buf, "    <td  bgcolor = \"{} 1 1\">{}</td>", hue, inner);

                    // Reset start so we don't erase colored nodes
                    start = curr;
                }
                for _ in start..interfere_portion {
                    writeln!(buf, "<td></td>");
                }
                writeln!(buf, "</tr>");
            }
        }
        writeln!(buf, "</table>>]");

        for e in cfg_succs.get(block).unwrap_or(&BTreeSet::new()) {
            writeln!(
                buf,
                "{} -> {}",
                block.as_str().replace('.', "_"),
                e.as_str().replace('.', "_")
            )
            .unwrap();
        }
    }

    writeln!(buf, "}}").unwrap();
    fs::write(&format!("{}.dot", file), buf).unwrap();
}
