pub use std::collections::{BTreeMap, HashMap, BinaryHeap};
pub use egg::*;

mod ematch;
pub use ematch::*;

mod compare;
pub use compare::*;

mod ex1;
pub use ex1::*;

mod ex2;
pub use ex2::*;

mod ctxt_cost;
pub use ctxt_cost::*;

mod misc;
pub use misc::*;

mod node_detour;
pub use node_detour::*;

mod pat_detour;
pub use pat_detour::*;

fn main() {
    run_ex2();
}
