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
    let n = 4;
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
    let st: RecExpr<Math> = init_term().parse().unwrap();
    println!("Initial: {st}");
    let mut eg = EGraph::new(());
    let i = eg.add_expr(&st);
    let rws = rules();

    eg.rebuild();
    for _ in 0..100 {
        detour_eqsat_iter(i, &rws, &mut eg);

        let ex = Extractor::new(&eg, AstSize);
        println!("Extracted: {}", ex.find_best(i).1);
    }
}
