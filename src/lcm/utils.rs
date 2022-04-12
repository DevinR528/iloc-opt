use std::collections::{hash_map::RandomState, BTreeSet, HashMap, HashSet, VecDeque};

use crate::ssa::OrdLabel;

/// This is parent -> children, where children is fall through then jump (ssa val
/// numbering needs this)
pub fn reverse_postorder<'a>(
    succs: &'a HashMap<OrdLabel, BTreeSet<OrdLabel>>,
    start: &'a OrdLabel,
) -> impl Iterator<Item = &'a OrdLabel> + 'a {
    postorder(succs, start).into_iter().rev()
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
            // This is fall through then jump or in traversal language left then right
            // child
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
