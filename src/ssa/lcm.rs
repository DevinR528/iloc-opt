use std::{
    collections::{btree_map::Entry, BTreeMap, BTreeSet},
    vec,
};

use crate::{
    iloc::Function,
    ssa::{preorder, DominatorTree, OrdLabel},
};

pub fn lazy_code_motion(func: &mut Function, domtree: &DominatorTree) {
    for blk in preorder(&domtree.cfg_succs_map, &OrdLabel::new_start(&func.label)) {}
}
