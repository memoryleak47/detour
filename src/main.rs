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

mod ex2;
pub use ex2::*;

mod minqueue;
pub use minqueue::*;


fn main() {
    run_ex2();
}
