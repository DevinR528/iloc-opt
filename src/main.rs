#![allow(unused)]

mod iloc;

use std::io::Read;

use iloc::{parse_text, Instruction};

fn main() {
    use std::collections::HashMap;
    use std::fs;

    let mut map = HashMap::new();

    let text = fs::read_to_string("./input.txt").unwrap();
    for line in text.split(&[' ', '\n'][..]) {
        if line.is_empty() {
            continue;
        }
        (*map.entry(line).or_insert(0_usize)) += 1;
    }

    // `count` is a reference to a usize or *usize in c
    // `&count` destructures the pointer doing a dereference
    //
    // it's like in c++ if you return a tuple you can
    // `auto [a, b] = tuple_return();`
    let mut totes = 0;
    for (word, &count) in map.iter() {
        totes += count;
        if count > 1 {
            println!("{} {}", word, count);
        }
    }
    println!("{}", totes);
}
