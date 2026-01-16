use egg::*;

use std::collections::{BTreeMap, HashMap, BinaryHeap};

type EG = EGraph<Math, ()>;

fn lookup_pat(pat: &PatternAst<Math>, eg: &EG, subst: &Subst) -> Option<Id> {
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

fn compute_detour_costs(id: Id, eg: &EG) -> BTreeMap<usize, Vec<Id>> {
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
        for e in &eg[i].nodes {
            let e_cost = AstSize.cost(e, |k| ex.find_best_cost(k));
            for &c in e.children() {
                let c_cost = ex.find_best_cost(c);
                let ncst = e_cost + cst - c_cost;
                queue.push((usize::MAX - ncst, c));
            }
        }
    }

    let mut dd: BTreeMap<usize, Vec<Id>> = Default::default();
    let opt_cost = ex.find_best_cost(id);
    for x in eg.classes() {
        let x = x.id;
        let det = ctxt_cost[&x] + ex.find_best_cost(x) - opt_cost;
        if !dd.contains_key(&det) {
            dd.insert(det, Vec::new());
        }
        dd.get_mut(&det).unwrap().push(x);
    }

    /*
        println!("===============");
        for (cst, xx) in dd.iter() {
            dbg!(cst);
            for x in xx {
                println!("{}", ex.find_best(*x).1);
            }
        }
        println!("===============");
    */

    dd
}

// one iteration of eqsat governed by the detour system.
fn detour_iter(id: Id, rws: &[Rewrite<Math, ()>], eg: &mut EG) {
    let dd = compute_detour_costs(id, eg);

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
    for i in 0..33 {
        s = format!("(+ (+ a{i} {s}) (- a{i}))");
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
    for _ in 0..5 {
        detour_iter(i, &rws, &mut eg);

        let ex = Extractor::new(&eg, AstSize);
        println!("Extracted: {}", ex.find_best(i).1);
    }
}
