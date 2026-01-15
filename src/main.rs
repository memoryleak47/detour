use egg::*;
use std::collections::BTreeMap;

struct DetourAnalysis;

// one iteration of eqsat governed by the detour system.
fn detour_iter<L: Language>(rws: &[Rewrite<L, DetourAnalysis>], eg: &mut EGraph<L, DetourAnalysis>) {
    let mut matches: Vec<(usize, SearchMatches<L>)> = Vec::new();

    let mut dd: BTreeMap<usize, Vec<Id>> = Default::default();
    for x in eg.classes() {
        let x = x.id;
        let det = detour_cost(x, eg);
        if !dd.contains_key(&det) {
            dd.insert(det, Vec::new());
        }
        dd.get_mut(&det).unwrap().push(x);
    }

    for (_, x) in &dd {
        let mut matches: Vec<(usize /*rw index*/, SearchMatches<L>)> = Vec::new();

        // TODO this rebuild shouldn't be necessary.
        eg.rebuild();

        for i in x {
            for (rw_i, rw) in rws.iter().enumerate() {
                if let Some(sm) = rw.searcher.search_eclass(eg, *i) {
                    matches.push((rw_i, sm));
                }
            }
        }

        let mut dirty = false;
        for (rw_i, sm) in matches {
            let changes = rws[rw_i].applier.apply_matches(eg, &[sm], rws[rw_i].name);
            if changes.len() > 0 { dirty = true; }
        }

        if dirty { break }
    }

    eg.rebuild();
}

fn detour_cost<L: Language>(id: Id, eg: &EGraph<L, DetourAnalysis>) -> usize {
    let dat = eg[id].data;
    dat.0 + dat.1
}

impl<L: Language> Analysis<L> for DetourAnalysis {
    type Data = (/*Cost*/usize, /*Ctxt Cost*/usize);

    fn make(eg: &mut EGraph<L, Self>, n: &L, i: Id) -> Self::Data {
        let cost = AstSize.cost(n, |i| eg[i].data.0);
        (cost, 0 /* TODO */)
    }

    fn merge(&mut self, d1: &mut Self::Data, d2: Self::Data) -> DidMerge {
        let v1 = *d1;
        let v2 = d2;

        let out = (v1.0.min(v2.0), 0 /* TODO */);
        *d1 = out;

        DidMerge(out != v1, out != v2)
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
