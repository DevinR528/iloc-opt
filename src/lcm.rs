mod lcm_impl;
mod licm;
mod utils;

pub use lcm_impl::{lazy_code_motion, print_maps};
pub use licm::{find_loops, LoopAnalysis, LoopInfo};
pub use utils::{postorder, reverse_postorder};
