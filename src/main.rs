use egg::*;

struct DetourAnalysis;

struct DetourScheduler;

impl<L: Language> RewriteScheduler<L, DetourAnalysis> for DetourScheduler {
    fn search_rewrite<'a>(&mut self, it: usize, eg: &EGraph<L, DetourAnalysis>, rw: &'a Rewrite<L, DetourAnalysis>) -> Vec<SearchMatches<'a, L>> {
        let mut out = Vec::new();
        let mut threshold = usize::MAX;
        for e in eg.classes() {
            let c = e.data;
            let detour_cost = c.0 + c.1;
            if detour_cost <= threshold {
                let new: Option<SearchMatches<L>> = rw.searcher.search_eclass(eg, e.id);
                if new.is_some() {
                    if detour_cost < threshold {
                        threshold = detour_cost;
                        out.clear();
                    }
                    out.extend(new);
                }
            }
        }
        out
    }
}

impl<L: Language> Analysis<L> for DetourAnalysis {
    type Data = (/*Cost*/usize, /*Ctxt Cost*/usize);

    fn make(eg: &mut EGraph<L, Self>, n: &L, i: Id) -> Self::Data {
        let cost = AstSize.cost(n, |i| eg[i].data.0);
        (cost, 0)
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

fn main() {
    let st = "(+ (+ b a) (- b))".parse().unwrap();
    let r: Runner<Math, DetourAnalysis> =
        Runner::new(DetourAnalysis)
            .with_expr(&st)
            .with_scheduler(DetourScheduler)
            .run(&rules());
    let ex = Extractor::new(&r.egraph, AstSize);
    println!("{}", ex.find_best(r.roots[0]).1);
}
