#![allow(unused)]

use std::{env, fs};

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
        println!("{}", file);

        let input = fs::read_to_string(file).unwrap();
        let mut iloc = parse_text(&input).unwrap();
        let blocks = make_blks(iloc);
        println!("{:?}", blocks.functions);
    }
}
