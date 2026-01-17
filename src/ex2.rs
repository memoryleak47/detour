use crate::*;

// Calculus is from here: https://ieeexplore.ieee.org/abstract/document/8146748

define_language! {
    pub enum Lambda {
        "lam" = Lam([Id; 1]),
        "app" = App([Id; 2]),
        "subst" = Subst([Id; 2]), // _ [ _ ]
        "compose" = Compose([Id; 2]), // _ ° _
        "dot" = Dot([Id; 2]), // _ . _
        "arrow" = Arrow,
        "one" = One,
        "id" = Id,
        Symbol(Symbol),
    }
}

fn rules() -> Vec<Rewrite<Lambda, ()>> {
    vec![
        rewrite!("beta"; "(app (lam ?a) ?b)" => "(subst ?a (dot ?b id))"),
        rewrite!("var-id"; "(subst one id)" => "one"),
        rewrite!("var-cons"; "(subst one (dot ?a ?s))" => "?a"),
        rewrite!("app"; "(subst (app ?a ?b) ?s)" => "(app (subst ?a ?s) (subst ?b ?s))"),
        rewrite!("abs"; "(subst (lam ?a) ?s)" => "(lam (subst ?a (dot one (compose ?s arrow))))"),
        rewrite!("clos"; "(subst (subst ?a ?s) ?t)" => "(subst ?a (compose ?s ?t))"),
        rewrite!("idL"; "(compose id ?s)" => "?s"),
        rewrite!("shiftId"; "(compose arrow (dot ?a ?s))" => "?s"),
        rewrite!("shiftCons"; "(compose arrow (dot ?a ?s))" => "?s"),
        rewrite!("map"; "(compose (dot ?a ?s) ?t)" => "(dot (subst ?a ?t) (compose ?s ?t))"),
        rewrite!("ass"; "(compose (compose ?s1 ?s2) ?s3)" => "(compose ?s1 (compose ?s2 ?s3))"),
    ]
}

fn init_term() -> String {
    format!("(app (lam one) (lam one))")
}

pub fn run_ex2() {
    compare(&init_term(), &rules());
}
