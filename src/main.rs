use egg::*;

struct DetourCost;

struct DetourScheduler;

impl<L: Language> RewriteScheduler<L, DetourCost> for DetourScheduler {
}

impl<L: Language> Analysis<L> for DetourCost {
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
        "-" = Sub([Id; 2]),
        "*" = Mul([Id; 2]),
        "/" = Div([Id; 2]),
        Symbol(Symbol),
    }
}

fn rules() -> Vec<Rewrite<Math, DetourCost>> {
    vec![
        rewrite!("cancel"; "(- ?a ?a)" => "z"),
        rewrite!("assoc-i"; "(+ (+ ?a ?b) ?c)" => "(+ ?a (+ ?b ?c))"),
        rewrite!("assoc-ii"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
    ]
}

fn main() {
    let st = "(+ a (- b b))".parse().unwrap();
    let r: Runner<Math, DetourCost> =
        Runner::new(DetourCost)
            .with_expr(&st)
            .with_scheduler(DetourScheduler)
            .run(&rules());
    let ex = Extractor::new(&r.egraph, AstSize);
    println!("{}", ex.find_best(r.roots[0]).1);
}
