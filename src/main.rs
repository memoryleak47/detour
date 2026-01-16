use egg::*;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::collections::BinaryHeap;

struct DetourAnalysis;

fn lookup_pat<L: Language>(pat: &PatternAst<L>, eg: &EGraph<L, DetourAnalysis>, subst: &Subst) -> Option<Id> {
    let mut vec = Vec::new();
    for i in 0..pat.len() {
        match &pat[i.into()] {
            ENodeOrVar::ENode(n) => {
                let mut n = n.clone().map_children(|k| vec[usize::from(k)]);
                let k = eg.lookup(&mut n)?;
                vec.push(k);
            },
            ENodeOrVar::Var(v) => vec.push(subst[*v]),
        }
    }
    vec.last().copied()
}

fn compute_detour_costs<L: Language>(id: Id, eg: &EGraph<L, ()>) -> HashMap<Id, usize> {
    let ex = Extractor::new(eg, AstSize);
    let mut ctxt_cost = HashMap::new();

    // as this queue is a max-heap, we'll store usize::MAX - ctxt_cost in the usize of queue.
    let mut queue: BinaryHeap<(usize, Id)> = BinaryHeap::new();

    // initial
    queue.push((usize::MAX - 0, id));

    while let Some((cst, i)) = queue.pop() {
        let cst = usize::MAX - cst;
        if ctxt_cost.contains_key(&i) { continue }
        ctxt_cost.insert(i, cst);
        for e in eg.nodes() {
            let e_cost = AstSize.cost(e, |k| ex.find_best_cost(k));
            for &c in e.children() {
                let c_cost = ex.find_best_cost(c);
                let ncst = e_cost - c_cost;
                queue.push((usize::MAX - ncst, c));
            }
        }
    }

    let mut out = HashMap::new();
    for i in eg.classes() {
        let i = i.id;
        out.insert(i, ctxt_cost[&i] + ex.find_best_cost(i));
    }
    out
}

// one iteration of eqsat governed by the detour system.
fn detour_iter<L: Language>(rws: &[Rewrite<L, DetourAnalysis>], eg: &mut EGraph<L, DetourAnalysis>) {
    let mut dd: BTreeMap<usize, Vec<Id>> = Default::default();
    for x in eg.classes() {
        let x = x.id;
        let det = detour_cost(x, eg);
        if !dd.contains_key(&det) {
            dd.insert(det, Vec::new());
        }
        dd.get_mut(&det).unwrap().push(x);
    }

    let mut new_apps: Vec<(/*rw index*/ usize, /*lhs*/ Id, Subst)> = Vec::new();

    for (_, x) in &dd {
        for i in x {
            for (rw_i, rw) in rws.iter().enumerate() {
                if let Some(sm) = rw.searcher.search_eclass(eg, *i) {
                    let rhs_pat = rw.applier.get_pattern_ast().unwrap();
                    for subst in sm.substs {
                        let rhs = lookup_pat(&rhs_pat, eg, &subst);
                        let lhs = sm.eclass;
                        if Some(lhs) != rhs {
                            new_apps.push((rw_i, lhs, subst));
                        }
                    }
                }
            }
        }

        for (rw_i, lhs, subst) in &new_apps {
            rws[*rw_i].applier.apply_one(eg, *lhs, subst, None, rws[*rw_i].name);
        }

        if new_apps.len() > 0 {
            eg.rebuild();
            break
        }
    }
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

    eg.rebuild();
    for _ in 0..5 {
        detour_iter(&rws, &mut eg);
    }
    let ex = Extractor::new(&eg, AstSize);
    println!("Extracted: {}", ex.find_best(i).1);
}
