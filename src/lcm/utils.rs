use std::collections::{hash_map::RandomState, BTreeSet, HashMap, HashSet, VecDeque};

use crate::{iloc::Block, ssa::OrdLabel};

#[allow(unused)]
fn print_blocks(blocks: &[Block]) {
    for blk in &*blocks {
        // if !matches!(blk.label.as_str(), ".L0:" | ".L1:" | ".L3:" | ".L7:") {
        //     continue;
        // }

        println!("{} [", blk.label);
        for inst in &blk.instructions {
            println!("  {:?}", inst);
        }
        println!("]");
    }
}

/// This is parent -> children, where children is fall through then jump (ssa val numbering needs
/// this)
pub fn reverse_postorder<'a>(
    succs: &'a HashMap<OrdLabel, BTreeSet<OrdLabel>>,
    start: &'a OrdLabel,
) -> impl Iterator<Item = &'a OrdLabel> + 'a {
    let mut stack = VecDeque::from_iter([start]);
    let mut seen = HashSet::<_, RandomState>::from_iter([start]);
    std::iter::from_fn(move || {
        let val = stack.pop_front()?;
        seen.insert(val);
        if let Some(set) = succs.get(val) {
            for child in set {
                if seen.contains(child) {
                    continue;
                }
                stack.push_front(child);
                seen.insert(child);
            }
        }
        Some(val)
    })
}

/// Preorder is parent, left, right traversal of the cfg graph.
pub fn preorder<'a>(
    succs: &'a HashMap<OrdLabel, BTreeSet<OrdLabel>>,
    start: &'a OrdLabel,
) -> impl Iterator<Item = &'a OrdLabel> + 'a {
    let mut stack = VecDeque::from_iter([start]);
    let mut seen = HashSet::<_, RandomState>::from_iter([start]);
    std::iter::from_fn(move || {
        let val = stack.pop_front()?;
        if let Some(set) = succs.get(val) {
            for child in set {
                if seen.contains(child) {
                    continue;
                }
                stack.push_back(child);
                seen.insert(child);
            }
        }
        seen.insert(val);

        Some(val)
    })
}

/// Postorder is left child, right child, parent. This is the reverse graph
pub fn postorder<'a>(
    succs: &'a HashMap<OrdLabel, BTreeSet<OrdLabel>>,
    start: &'a OrdLabel,
) -> Vec<&'a OrdLabel> {
    fn _postord<'a>(
        succs: &'a HashMap<OrdLabel, BTreeSet<OrdLabel>>,
        root: &'a OrdLabel,
        collected: &mut Vec<&'a OrdLabel>,
        seen: &mut HashSet<&'a OrdLabel>,
    ) {
        // Protects against loops
        seen.insert(root);
        if let Some(set) = succs.get(root) {
            // This is fall through then jump or in traversal language left then right child
            for child in set.iter() {
                if seen.contains(child) {
                    continue;
                }
                _postord(succs, child, collected, seen);
            }
        }
        collected.push(root);
    }

    let mut order = vec![];
    let mut seen = HashSet::new();
    _postord(succs, start, &mut order, &mut seen);
    order
}

pub fn dfs_order<'a>(
    succs: &'a HashMap<OrdLabel, BTreeSet<OrdLabel>>,
    start: &'a OrdLabel,
) -> Vec<&'a OrdLabel> {
    fn _postord<'a>(
        succs: &'a HashMap<OrdLabel, BTreeSet<OrdLabel>>,
        root: &'a OrdLabel,
        collected: &mut Vec<&'a OrdLabel>,
        seen: &mut HashSet<&'a OrdLabel>,
    ) {
        // Protects against loops
        seen.insert(root);
        collected.push(root);

        if let Some(set) = succs.get(root) {
            // This is fall through then jump or in traversal language left then right child
            for child in set.iter() {
                if seen.contains(child) {
                    continue;
                }
                _postord(succs, child, collected, seen);
            }
        }
    }

    let mut order = vec![];
    let mut seen = HashSet::new();
    _postord(succs, start, &mut order, &mut seen);
    order
}
