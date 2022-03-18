use std::{
    collections::{btree_map::Entry, BTreeMap, BTreeSet, HashSet},
    vec,
};

use crate::{
    iloc::{Function, Reg},
    ssa::{dfs_order, postorder, preorder, reverse_postorder, DominatorTree, OrdLabel},
};

// Critical edge - These must be split
// Critical edges are edges from a block with multiple successors to a block
// with multiple predecessors.
//
//     N
//    / \ <-- this is critical
//       \ / <-- this is another predecessor
//        C
//

pub fn lazy_code_motion(func: &mut Function, domtree: &DominatorTree) {
    let start = OrdLabel::new_start(&func.label);

    // BOOK anticipated
    let mut antic_loc: HashSet<Reg> = HashSet::new();
    let mut kill: HashSet<Reg> = HashSet::new();
    for blk in reverse_postorder(&domtree.cfg_succs_map, &start)
        .filter_map(|label| func.blocks.iter().find(|b| b.label.starts_with(label.as_str())))
    {
        println!("{}", blk.label);
        for inst in &blk.instructions {
            let (a, b) = inst.operands();
            let dst = inst.target_reg();
            if let Some(t) = dst {
                if !antic_loc.contains(t) && !kill.contains(t) {
                    antic_loc.insert(*t);
                }
            }
            for op in a.into_iter().chain(b).filter_map(|r| r.opt_reg()) {
                kill.insert(op);
            }
        }
        println!(
            "in anticipated {} {:?}",
            blk.label,
            antic_loc.difference(&kill).collect::<Vec<_>>()
        );
        println!("in kill {} {:?}", blk.label, kill.difference(&antic_loc).collect::<Vec<_>>());
    }

    // LLVM anticipated collection
    let mut changed = true;
    while changed {
        changed = false;
        for blk in reverse_postorder(&domtree.cfg_succs_map, &start)
            .filter_map(|label| func.blocks.iter().find(|b| b.label.starts_with(label.as_str())))
        {
            for inst in &blk.instructions {
                let dst = inst.target_reg();
            }
        }
    }

    // LLVM marking of instructions for PRE
    changed = true;
    while changed {
        changed = false;
        for blk in dfs_order(&domtree.cfg_succs_map, &start) {
            if blk == &start {
                continue;
            }

            for inst in func
                .blocks
                .iter()
                .find(|b| b.label.starts_with(blk.as_str()))
                .map_or(&[] as &[_], |b| &b.instructions)
            {
                changed |= instruction_pre();
            }
        }
    }
}

fn instruction_pre() -> bool {
    false
}
