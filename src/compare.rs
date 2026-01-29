use crate::*;
use std::fmt::Display;

pub fn compare<L: Language + Display + FromOp>(init_term: &str, rws: &[Rewrite<L, ()>], stop_size: usize) {
    eqsat_pat_detour(init_term, rws, stop_size);

    println!();
    println!("=============================================================================================");
    println!("=============================================================================================");
    println!();

    eqsat_normal(init_term, rws, stop_size);
}

pub fn eqsat_normal<L: Language + Display + FromOp>(init_term: &str, rws: &[Rewrite<L, ()>], stop_size: usize) {
    let st: RecExpr<L> = init_term.parse().unwrap();
    println!("Initial: {st}");
    let r: Runner<L, ()> =
        Runner::new(())
            .with_expr(&st)
            // .with_scheduler(SimpleScheduler)
            .with_node_limit(1_000_000)
            .with_iter_limit(40)
            .with_hook(move |r| {
                let ex = Extractor::new(&r.egraph, AstSize);
                if ex.find_best_cost(r.roots[0]) <= stop_size { return Err(format!("reached stop size!")) }
                Ok(())
            })
            .run(rws);
    dbg!(r.stop_reason);
    let ex = Extractor::new(&r.egraph, AstSize);
    println!("Normal Extracted: {}", ex.find_best(r.roots[0]).1);
    println!("Total Size: {}", r.egraph.total_size());
}
