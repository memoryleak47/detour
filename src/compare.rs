use crate::*;
use std::fmt::Display;

pub const STOP_SIZE: usize = 3;

pub fn compare<L: Language + Display + FromOp>(init_term: &str, rws: &[Rewrite<L, ()>]) {
    eqsat_pat_detour(init_term, rws, STOP_SIZE);

    println!();
    println!("=============================================================================================");
    println!("=============================================================================================");
    println!();

    eqsat_normal(init_term, rws);
}

pub fn eqsat_normal<L: Language + Display + FromOp>(init_term: &str, rws: &[Rewrite<L, ()>]) {
    let st: RecExpr<L> = init_term.parse().unwrap();
    println!("Initial: {st}");
    let r: Runner<L, ()> =
        Runner::new(())
            .with_expr(&st)
            .with_node_limit(1_000_000)
            .with_iter_limit(40)
            .with_hook(|r| {
                let ex = Extractor::new(&r.egraph, AstSize);
                if ex.find_best_cost(r.roots[0]) <= STOP_SIZE { return Err(format!("reached stop size!")) }
                Ok(())
            })
            .run(rws);
    dbg!(r.stop_reason);
    let ex = Extractor::new(&r.egraph, AstSize);
    println!("Normal Extracted: {}", ex.find_best(r.roots[0]).1);
    println!("Total Size: {}", r.egraph.total_size());
}
