use egg::*;

struct DetourAnalysis;

// one iteration of eqsat governed by the detour system.
fn detour_iter<L: Language>(rws: &[Rewrite<L, DetourAnalysis>], eg: &mut EGraph<L, DetourAnalysis>) {
    let mut matches: Vec<_> = Vec::new();
    for rw in rws {
        let s = rw.searcher.search(eg);
        matches.push(s);
    }

    for (rw, matches) in rws.iter().zip(matches.into_iter()) {
        rw.applier.apply_matches(eg, &matches, rw.name);
    }

    // TODO actually use the detour cost.

    eg.rebuild();
}

impl<L: Language> Analysis<L> for DetourAnalysis {
    type Data = (/*Cost*/usize, /*Ctxt Cost*/usize);

    fn make(eg: &mut EGraph<L, Self>, n: &L, i: Id) -> Self::Data {
        let cost = AstSize.cost(n, |i| eg[i].data.0);
        (cost, 0 /* TODO */)
    }

    fn merge(&mut self, d1: &mut Self::Data, d2: Self::Data) -> DidMerge {
        d1.0 = d1.0.min(d2.0);
        DidMerge(false, false)
    }
}

define_language! {
    pub enum Math {
        "+" = Add([Id; 2]),
        "-" = Sub([Id; 1]),
        "*" = Mul([Id; 2]),
        "/" = Div([Id; 1]),
        Symbol(Symbol),
    }
}

fn rules() -> Vec<Rewrite<Math, DetourAnalysis>> {
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
    for i in 0..5 {
        s = format!("(+ (+ a{i} {s}) (- a{i}))");
    }
    s
}

fn main() {
    let st: RecExpr<Math> = init_term().parse().unwrap();
    println!("Initial: {st}");
    let mut eg = EGraph::new(DetourAnalysis);
    let i = eg.add_expr(&st);
    let rws = rules();
    for _ in 0..5 {
        detour_iter(&rws, &mut eg);
    }
    let ex = Extractor::new(&eg, AstSize);
    println!("Extracted: {}", ex.find_best(i).1);
}
