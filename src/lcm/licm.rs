use std::{
    collections::{btree_map::Entry, BTreeMap, BTreeSet, HashMap},
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

pub struct LoopAnalysis {
    loop_map: HashMap<String, LoopInfo>,
}

impl LoopAnalysis {
    pub fn loop_map(&self) -> &HashMap<String, LoopInfo> {
        &self.loop_map
    }

    pub fn is_nested(&self, child: &OrdLabel) -> bool {
        let mut child = child.as_str();
        loop {
            match self.loop_map.get(child) {
                Some(LoopInfo::Loop { parent: Some(..), .. }) => return true,
                Some(LoopInfo::PartOf(lp)) => {
                    child = lp;
                }
                _ => return false,
            }
        }
    }

    pub fn level_of_nesting(&self, child: &OrdLabel) -> u32 {
        let mut child = child.as_str();
        let mut count = 0;
        loop {
            match self.loop_map.get(child) {
                Some(LoopInfo::Loop { parent: Some(lp), .. }) => {
                    count += 1;
                    child = lp;
                }
                Some(LoopInfo::Loop { parent: None, .. }) => {
                    count += 1;
                    return count;
                }
                Some(LoopInfo::PartOf(lp)) => {
                    child = lp;
                }
                _ => return count,
            }
        }
    }
}

pub fn find_loops(func: &mut Function, domtree: &DominatorTree) -> LoopAnalysis {
    // println!("{:#?}", domtree);
    let start = OrdLabel::new_start(&func.label);
    let mut loops = BTreeMap::<_, String>::new();
    let mut loop_ord = vec![];
    // We traverse the CFG in reverse postorder
    for blk in reverse_postorder(&domtree.cfg_succs_map, &start) {
        // We check each predecessor of the control flow graph
        for pred in domtree.cfg_preds_map.get(blk).unwrap_or(&BTreeSet::default()) {
            // If the block dominates one of it's preds it is a back edge to a loop
            if domtree.dom_tree.get(blk).map_or(false, |set| set.contains(pred)) {
                if loops.insert(blk.to_string(), blk.to_string()).is_none() {
                    loop_ord.push(blk.as_str());
                }
                // We only need to identify one back edge to know we are in a loop
                break;
            }
        }
    }

    let empty = BTreeSet::default();
    let mut loop_map = loops
        .iter()
        .map(|(k, v)| (k.clone(), LoopInfo::new(v)))
        .collect::<BTreeMap<_, _>>();
    let mut stack = vec![];
    let mut seen = BTreeSet::new();
    // Iterate over the known loops to find the blocks they "own" as part of their loop,
    // this also determines which loops are nested in in other loops
    for lp in loop_ord.into_iter().rev() {
        for pred in domtree.cfg_preds_map.get(lp).unwrap_or(&empty) {
            // Add the back edges to the stack/worklist
            if domtree.dom_tree.get(lp).map_or(false, |set| set.contains(pred)) {
                stack.push(pred.as_str());
            }
        }

        while let Some(node) = stack.pop() {
            let mut continue_dfs = None;
            if let Entry::Vacant(unseen) = loop_map.entry(node.to_string()) {
                unseen.insert(LoopInfo::PartOf(lp.to_string()));
                continue_dfs = Some(node.to_string());
            } else if let Some(node_loop) = loop_map.get(node) {
                let mut node_loop = node_loop.header().to_string();
                let mut nlp_opt = loop_map.get(&node_loop).and_then(|l| l.parent());

                while let Some(nlp) = nlp_opt {
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
                            match loop_map.entry(key) {
                                Entry::Occupied(mut o) => match o.get_mut() {
                                    LoopInfo::Loop { parent, .. } => {
                                        *parent = Some(lp.to_string())
                                    }
                                    it => panic!("{} {:?}", node_loop, it),
                                },
                                it => panic!("{} {:?}", node_loop, it),
                            }
                            continue_dfs = Some(node_loop)
                        } else {
                            // `lp` is a one block loop (loop over itself)
                            continue_dfs = None;
                        }
                    }
                }
            }

            if let Some(cont) = continue_dfs {
                for blk in domtree.cfg_preds_map.get(cont.as_str()).unwrap_or(&empty) {
                    if !seen.contains(blk.as_str()) {
                        stack.push(blk.as_str());
                    }
                    seen.insert(blk.as_str());
                }
            }
        }
    }

    LoopAnalysis { loop_map: loop_map.into_iter().collect() }
}
