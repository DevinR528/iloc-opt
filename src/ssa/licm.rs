use std::{
    collections::{btree_map::Entry, BTreeMap, BTreeSet},
    vec,
};

use crate::{
    iloc::Function,
    ssa::{reverse_postorder, DominatorTree, OrdLabel},
};

#[derive(Debug)]
pub enum LoopInfo {
    Loop { header: String, parent: Option<String> },
    PartOf(String),
}
impl LoopInfo {
    pub fn new(header: &str) -> Self {
        Self::Loop { header: header.to_string(), parent: None }
    }
    pub fn header(&self) -> &str {
        match self {
            LoopInfo::Loop { header, .. } | LoopInfo::PartOf(header) => header,
        }
    }
    pub fn parent(&self) -> Option<&str> {
        if let LoopInfo::Loop { parent, .. } = self {
            parent.as_deref()
        } else {
            None
        }
    }
}

pub fn find_loops(func: &mut Function, domtree: &DominatorTree) {
    // println!("{:#?}", domtree);
    let start = OrdLabel::new_start(&func.label);
    let mut loops = BTreeMap::<_, String>::new();
    let mut loop_ord = vec![];
    // We traverse the CFG in reverse postorder
    for blk in reverse_postorder(&domtree.cfg_succs_map, &start) {
        // We check each predecessor of the control flow graph
        for pred in domtree.cfg_preds_map.get(blk).unwrap_or(&BTreeSet::default()) {
            // If the block dominates one of it's preds it is a back edge to a loop
            if domtree.dom_frontier_map.get(pred).map_or(false, |set| set.contains(blk)) {
                if loops.insert(blk.to_string(), blk.to_string()).is_none() {
                    loop_ord.push(blk.as_str());
                }
                // We only need to identify one back edge to know we are in a loop
                break;
            }
        }
    }

    let empty = BTreeSet::default();
    let mut loop_map =
        loops.iter().map(|(k, v)| (k.clone(), LoopInfo::new(v))).collect::<BTreeMap<_, _>>();
    let mut stack = vec![];
    for lp in loop_ord.into_iter().rev() {
        for pred in domtree.cfg_preds_map.get(lp).unwrap_or(&empty) {
            // Add the back edges to the stack/worklist
            if domtree.dom_frontier_map.get(pred).map_or(false, |set| set.contains(lp)) {
                stack.push(pred.as_str());
            }
        }

        while let Some(node) = stack.pop() {
            // println!("{:#?}", loop_map);
            let mut continue_dfs = None;
            if let Entry::Vacant(unseen) = loop_map.entry(node.to_string()) {
                unseen.insert(LoopInfo::PartOf(lp.to_string()));
                continue_dfs = Some(node.to_string());
            } else if let Some(node_loop) = loop_map.get(node) {
                let mut node_loop = node_loop.header().to_string();
                let mut nlp_opt = loop_map.get(&node_loop).and_then(|l| l.parent());

                println!("{:?} {} {}", nlp_opt, node_loop, lp);

                while let Some(nlp) = nlp_opt {
                    // println!("{} {}", nlp, lp);
                    if nlp == lp {
                        // We have walked back to the start of the loop
                        break;
                    } else {
                        node_loop = nlp.to_string();
                        nlp_opt = loop_map.get(&node_loop).and_then(|n| n.parent());
                    }
                }

                // We either have `nlp_opt` as `None` and `node_loop` is a new inner loop
                // or `nlp_opt` is `Some` and `node_loop` is a known inner loop
                match nlp_opt {
                    Some(..) => continue_dfs = None,
                    None => {
                        if node_loop != lp {
                            let key = node_loop.to_string();
                            println!("Parent {} {}", key, lp);
                            println!("{:?}", loop_map);
                            match loop_map.entry(key) {
                                Entry::Occupied(mut o) => match o.get_mut() {
                                    LoopInfo::Loop { parent, .. } => *parent = Some(lp.to_string()),
                                    it => panic!("{} {:?}", node_loop, it),
                                },
                                it => panic!("{} {:?}", node_loop, it),
                            }
                            continue_dfs = Some(node_loop)
                        } else {
                            continue_dfs = None;
                        }
                    }
                }
            }

            if let Some(cont) = continue_dfs {
                for blk in domtree.cfg_preds_map.get(cont.as_str()).unwrap_or(&empty) {
                    stack.push(blk.as_str());
                }
            }
        }
    }

    println!("{:#?}", loop_map);
}
