#![feature(
	let_else,
	map_first_last,
	once_cell,
	stmt_expr_attributes,
	let_chains,
	try_blocks,
	drain_filter,
	default_free_fn,
	if_let_guard,
	core_intrinsics
)]
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
mod label;

// Each pass of our optimizing compiler
//
/// ## Local Value Numbering
/// Working on extended basic blocks we remove redundant expressions and fold constants.
mod loc_val_num;

/// ## Lazy Code Motion
/// Removes the SSA numbering and runs lcm or partial redundancy elimination.
mod lcm;

/// ## Single Static Assignment
/// Build SSA form of the program and runs all optimizations that rely on SSA.
mod ssa;

/// ## Register Allocation
/// Using live ranges, an interference graph, and coloring of that graph we allocate
/// registers for our currently infinite set.
mod ralloc;

use iloc::{make_blks, parse_text};
use label::OrdLabel;
use lcm::lazy_code_motion;
use ralloc::K_DEGREE;
#[allow(unused)]
use ssa::{build_cfg, dominator_tree, ssa_optimization};

use crate::{
	iloc::{make_basic_blocks, Instruction},
	ssa::RenameMeta,
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
			unsafe { SSA = true; }
			files
		}
		["opt", reg_count, files @ ..] if let Ok(number_registers) = reg_count.parse::<usize>() => {
			unsafe { K_DEGREE = number_registers; }
			optimize = true;
			files
		}
		["opt", files @ ..] => {
			// Defaults to 12 real registers for register allocation
			unsafe { K_DEGREE = 12; }

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

			// LVN (local value numbering)
			for func in &mut blocks.functions {
				for blk in &mut func.blocks {
					if let Some(insts) = loc_val_num::number_basic_block(blk) {
						blk.instructions = insts;
					}
				}
			}

			// SSA (dominator based value numbering redundancy elimination and dead code
			// elimination)
			let mut blocks = make_basic_blocks(&blocks);
			let func_domtree = ssa::ssa_optimization(&mut blocks);

			// PRE/LCM (partial redundancy elimination/lazy code motion)
			for func in &mut blocks.functions {
				for blk in &mut func.blocks {
					for inst in &mut blk.instructions {
						inst.remove_phis();
					}
				}
				lazy_code_motion(func, func_domtree.get(&func.label).unwrap());
			}

			// REGISTER ALLOCATION
			ralloc::allocate_registers(&mut blocks);

			println!("optimization done {}ms", now.elapsed().as_millis());

			let mut buf = String::new();
			for inst in blocks.instruction_iter() {
				if matches!(inst, Instruction::Skip(..)) {
					// continue;
				}
				buf.push_str(&inst.to_string())
			}

			let mut path = PathBuf::from(&file);
			let file = path.file_stem().unwrap().to_string_lossy().to_string();
			path.set_file_name(&format!("{}.lvn.dbre.dce.pre.ra.il", file));
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
				let dtree = dominator_tree(&cfg, &mut func.blocks);
				let phis =
					ssa::insert_phi_functions(func, &dtree.cfg_succs_map, &dtree.dom_frontier_map);

				let mut meta = HashMap::new();
				for (_blk_label, register_set) in phis {
					meta.extend(register_set.iter().map(|op| (*op, RenameMeta::default())));
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
