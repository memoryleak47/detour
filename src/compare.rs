use crate::*;
use std::fmt::Display;

pub fn compare<L: Language + Display + FromOp>(init_term: &str, rws: &[Rewrite<L, ()>]) {
    eqsat_node_detour(init_term, rws);
    println!("------------------------------");
    eqsat_normal(init_term, rws);
}

pub fn eqsat_node_detour<L: Language + Display + FromOp>(init_term: &str, rws: &[Rewrite<L, ()>]) {
    let st: RecExpr<L> = init_term.parse().unwrap();
    println!("Initial: {st}");
    let mut eg = EGraph::new(());
    let i = eg.add_expr(&st);

    eg.rebuild();
    for _ in 0..70 {
        node_detour_eqsat_step(i, rws, &mut eg);

        let ex = Extractor::new(&eg, AstSize);
        println!("Detour Extracted: {}", ex.find_best(i).1);
    }
    println!("Total Size: {}", eg.total_size());
}

pub fn eqsat_normal<L: Language + Display + FromOp>(init_term: &str, rws: &[Rewrite<L, ()>]) {
    let st: RecExpr<L> = init_term.parse().unwrap();
    println!("Initial: {st}");
    let r: Runner<L, ()> =
        Runner::new(())
            .with_expr(&st)
            .with_node_limit(1_000_000)
            .with_iter_limit(40)
            .run(rws);
    dbg!(r.stop_reason);
    let ex = Extractor::new(&r.egraph, AstSize);
    println!("Normal Extracted: {}", ex.find_best(r.roots[0]).1);
    println!("Total Size: {}", r.egraph.total_size());
}
