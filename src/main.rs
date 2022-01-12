#![allow(unused)]

use std::{env, fs, io::Write, path::PathBuf};

// Our Instruction definition
mod iloc;

// Each pass of our optimizing compiler
//
// Local Value Numbering
mod loc_val_num;

use iloc::{make_blks, parse_text, Instruction};

const JAVA_ILOC_BENCH: &str = "java -jar ~/Downloads/my-cs6810-ssa-opt-project/iloc.jar -s";
const JAVA_ILOC_DEBUG: &str = "java -jar ~/Downloads/my-cs6810-ssa-opt-project/iloc.jar -d";

fn main() {
    let files = env::args().skip(1).collect::<Vec<_>>();

    for file in files {
        println!("performing optimization on: {}", file);

        let input = fs::read_to_string(&file).unwrap();
        let mut iloc = parse_text(&input).unwrap();
        let mut blocks = make_blks(iloc);
        for func in &mut blocks.functions {
            for blk in &mut func.blk {
                if let Some(insts) = loc_val_num::number_basic_block(blk.clone()) {
                    blk.instructions = insts;
                }
            }
        }

        let mut buf = String::new();
        for inst in blocks.instruction_iter() {
            // println!("{:?}", inst);
            buf.push_str(&inst.to_string())
        }

        let mut path = PathBuf::from(&file);
        let file = path.file_stem().unwrap().to_string_lossy().to_string();
        path.set_file_name(&format!("opt.{}.il", file));

        let mut fd = fs::OpenOptions::new()
            .create(true)
            .truncate(true)
            .write(true)
            .open(&path)
            .unwrap();

        fd.write_all(buf.as_bytes()).unwrap();
    }
}
