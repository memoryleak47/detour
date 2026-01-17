use crate::*;

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
        // Calculus is from here: https://ieeexplore.ieee.org/abstract/document/8146748
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

// zero = \x. \y. y
// zero = \. \. 1
fn zero() -> String {
    format!("(lam (lam one))")
}

// suc a = \x. \y. x a
// suc a = \. \. 2 a
fn suc(a: &str) -> String {
    let v2 = var(2);
    format!("(lam (lam (app {v2} {a})))")
}

// The smallest var is 1.
fn var(i: usize) -> String {
    assert!(i>0);

    let mut o = format!("one");
    for _ in 1..i {
        o = format!("(subst {o} arrow)");
    }
    o
}

// returns Y f
fn fix(f: &str) -> String {
    let omega = format!("(lam (app {f} (app one one)))");
    format!("{omega} {omega}")
}

// pred n = \x. \y. n x y
// pred n = \. \. n 2 1
fn pred(n: &str) -> String {
    let v2 = var(2);
    let v1 = var(1);
    format!("(lam (lam (app (app {n} {v2}) {v1})))")
}

fn init_term() -> String {
    let mut x = zero();
    let k = 1;
    for _ in 0..k {
        x = suc(&x);
    }
    for _ in 0..k {
        x = pred(&x);
    }
    x
}

pub fn run_ex2() {
    compare(&init_term(), &rules());
}
