mod lcm;
mod licm;
mod utils;

pub use lcm::lazy_code_motion;
pub use licm::{find_loops, LoopAnalysis, LoopInfo};
pub use utils::{dfs_order, postorder, preorder, reverse_postorder};
