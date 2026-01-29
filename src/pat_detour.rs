use crate::*;
use std::fmt::Display;

pub fn pat_detour_eqsat_step<L: Language + Display>(root: Id, rws: &[Rewrite<L, ()>], eg: &mut EGraph<L, ()>) {
    let ex = Extractor::new(&eg, AstSize);

    todo!()
}
