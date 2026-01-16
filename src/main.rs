use egg::*;

mod ematch;
pub use ematch::*;

mod detour;
pub use detour::*;

mod eqsat;
pub use eqsat::*;

use std::collections::{BTreeMap, HashMap, BinaryHeap};

pub type EG = EGraph<Math, ()>;

define_language! {
    pub enum Math {
        "+" = Add([Id; 2]),
        "-" = Sub([Id; 1]),
        "*" = Mul([Id; 2]),
        "/" = Div([Id; 1]),
        Symbol(Symbol),
    }
}

fn rules() -> Vec<Rewrite<Math, ()>> {
    vec![
        rewrite!("neg_cancel"; "(+ ?a (- ?a))" => "zero"),
        rewrite!("div_cancel"; "(* ?a (/ ?a))" => "one"),

        rewrite!("plus_zero"; "(+ ?a zero)" => "?a"),
        rewrite!("mul_zero"; "(* ?a zero)" => "zero"),
        rewrite!("mul_one"; "(* ?a one)" => "?a"),

        rewrite!("comm+"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rewrite!("comm*"; "(* ?a ?b)" => "(* ?b ?a)"),

        rewrite!("assoc-i"; "(+ (+ ?a ?b) ?c)" => "(+ ?a (+ ?b ?c))"),
        rewrite!("assoc-ii"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),

        rewrite!("distr-i"; "(* ?a (+ ?b ?c))" => "(+ (* ?a ?b) (* ?a ?c))"),
        rewrite!("distr-ii"; "(+ (* ?a ?b) (* ?a ?c))" => "(* ?a (+ ?b ?c))"),
    ]
}

fn init_term() -> String {
    let mut s = String::from("zero");
    let mut v = Vec::new();
    let n = 10;
    for i in 0..n {
        let j = (i+n/2)%n;
        v.push(format!("a{i}"));
        v.push(format!("(- a{j})"));
    }
    for x in v {
        s = format!("(+ {s} {x})");
    }
    s
}

fn main() {
    main_detour();
    // main_normal();
}

fn main_detour() {
    let st: RecExpr<Math> = init_term().parse().unwrap();
    println!("Initial: {st}");
    let mut eg = EGraph::new(());
    let i = eg.add_expr(&st);
    let rws = rules();

    eg.rebuild();
    for _ in 0..7 {
        detour_eqsat_iter(i, &rws, &mut eg);

        let ex = Extractor::new(&eg, AstSize);
        println!("Extracted: {}", ex.find_best(i).1);
    }
}

fn main_normal() {
    let st: RecExpr<Math> = init_term().parse().unwrap();
    println!("Initial: {st}");
    let r: Runner<Math, ()> =
        Runner::new(())
            .with_expr(&st)
            .with_node_limit(1_000_000)
            .with_iter_limit(40)
            .run(&rules());
    dbg!(r.stop_reason);
    let ex = Extractor::new(&r.egraph, AstSize);
    println!("Extracted: {}", ex.find_best(r.roots[0]).1);
}
