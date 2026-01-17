pub use std::collections::{BTreeMap, HashMap, BinaryHeap};
pub use egg::*;

mod ematch;
pub use ematch::*;

mod detour;
pub use detour::*;

mod eqsat;
pub use eqsat::*;

mod compare;
pub use compare::*;

mod ex1;
pub use ex1::*;


fn main() {
    run_ex1();
}
