#![feature(let_else, map_first_last, once_cell, stmt_expr_attributes, let_chains, try_blocks)]
#![allow(unused)]

use std::{
    collections::{HashMap, VecDeque},
    env, fs,
    io::Write,
    path::{Path, PathBuf},
    time::Instant,
};

// Our Instruction definition
mod iloc;
mod interp;

// Each pass of our optimizing compiler
//
/// Local Value Numbering
mod loc_val_num;
/// Build a single static assingment
mod ssa;

use iloc::{make_blks, parse_text};
#[allow(unused)]
use ssa::{build_cfg, dominator_tree, ssa_optimization};

use crate::{
    iloc::{make_basic_blocks, Instruction},
    ssa::{reverse_postorder, OrdLabel, RenameMeta},
};

const JAVA_ILOC_BENCH: &[&str] =
    &["-jar", "/home/devinr/Downloads/my-cs6810-ssa-opt-project/iloc.jar", "-s"];

pub static mut SSA: bool = false;

fn main() {
    let mut debug = false;
    let mut optimize = false;
    let files = env::args().skip(1).collect::<Vec<_>>();
    let f = files.iter().map(|s| s.as_str()).collect::<Vec<_>>();
    let files = match f.as_slice() {
        ["debug", files @ ..] => {
            debug = true;
            files
        }
        ["ssa", files @ ..] => {
            unsafe {
                SSA = true;
            }
            files
        }
        ["opt", files @ ..] => {
            optimize = true;
            files
        }
        [files @ ..] => files,
    };
    let ssa = unsafe { SSA };
    for file in files {
        let buf = if optimize && !ssa {
            println!("performing optimization on: {}", file);
            let input = fs::read_to_string(&file).unwrap();

            let now = Instant::now();
            let iloc = parse_text(&input).unwrap();
            let mut blocks = make_blks(iloc);
            for func in &mut blocks.functions {
                for blk in &mut func.blocks {
                    if let Some(insts) = loc_val_num::number_basic_block(blk) {
                        blk.instructions = insts;
                    }
                }
            }
            let mut blocks = make_basic_blocks(&blocks);
            ssa::ssa_optimization(&mut blocks);
            println!("optimization done {}ms", now.elapsed().as_millis());

            let mut buf = String::new();
            for inst in blocks.instruction_iter() {
                if matches!(inst, Instruction::Skip(..)) {
                    continue;
                }
                // println!("{:?}", inst);
                buf.push_str(&inst.to_string())
            }

            let mut path = PathBuf::from(&file);
            let file = path.file_stem().unwrap().to_string_lossy().to_string();
            path.set_file_name(&format!("{}.lvn.dbre.dce.pre.il", file));
            let mut fd =
                fs::OpenOptions::new().create(true).truncate(true).write(true).open(&path).unwrap();
            fd.write_all(buf.as_bytes()).unwrap();

            fs::read_to_string(&path).unwrap()
        } else if ssa {
            println!("performing ssa numbering on: {}", file);
            let input = fs::read_to_string(&file).unwrap();
            let iloc = parse_text(&input).unwrap();

            let mut blocks = make_basic_blocks(&make_blks(iloc));
            for func in &mut blocks.functions {
                let cfg = build_cfg(func);
                let start = OrdLabel::new_start(&func.label);

                let dtree = dominator_tree(&cfg, &mut func.blocks, &start);
                let phis = ssa::insert_phi_functions(
                    func,
                    &dtree.cfg_succs_map,
                    &start,
                    &dtree.dom_frontier_map,
                );

                let mut meta = HashMap::new();
                for (_blk_label, register_set) in phis {
                    meta.extend(register_set.iter().map(|op| (op.clone(), RenameMeta::default())));
                }
                let mut stack = VecDeque::new();
                // Label but don't remove any with the `SSA` flag on
                ssa::dom_val_num(&mut func.blocks, 0, &mut meta, &dtree, &mut stack);
            }

            let mut buf = String::new();
            for inst in blocks.instruction_iter() {
                buf.push_str(&inst.to_string())
            }

            let mut path = PathBuf::from(&file);
            let file = path.file_stem().unwrap().to_string_lossy().to_string();
            path.set_file_name(&format!("{}.ssa.il", file));
            let mut fd =
                fs::OpenOptions::new().create(true).truncate(true).write(true).open(&path).unwrap();
            fd.write_all(buf.as_bytes()).unwrap();

            fs::read_to_string(&path).unwrap()
        } else {
            fs::read_to_string(&file).unwrap()
        };

        interp::run_interpreter(make_blks(parse_text(&buf).unwrap()), debug).unwrap();
    }
}

#[allow(unused)]
fn java_run(path: &Path) {
    let cmd = std::process::Command::new("java")
        .args(JAVA_ILOC_BENCH.iter().chain(path.to_str().iter()).collect::<Vec<_>>())
        .output()
        .unwrap();

    if !cmd.stderr.is_empty() {
        eprint!("{}", String::from_utf8_lossy(&cmd.stderr));
    } else {
        print!("{}", String::from_utf8_lossy(&cmd.stdout));
    }
}
