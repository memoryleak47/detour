use crate::*;

define_language! {
    pub enum Math {
        "+" = Add([Id; 2]),
        "-" = Sub([Id; 1]),
        "*" = Mul([Id; 2]),
        "/" = Div([Id; 1]),
        Symbol(Symbol),
    }
}

fn random_math(size: usize, rng: &mut impl rand::Rng) -> RecExpr<Math> {
    let mut re = RecExpr::default();
    re.add(Math::Symbol(Symbol::from("zero")));
    re.add(Math::Symbol(Symbol::from("one")));
    re.add(Math::Symbol(Symbol::from("a")));

    for _ in 0..size {
        let id0 = Id::from(rng.gen_range(0..re.len()));
        let id1 = Id::from(rng.gen_range(0..re.len()));

        let n = match rng.gen_range(0..4) {
            0 => Math::Add([id0, id1]),
            1 => Math::Sub([id0]),
            2 => Math::Mul([id0, id1]),
            _ => Math::Div([id0]),
        };
        re.add(n);
    }
    re
}

fn rules() -> Vec<Rewrite<Math, ()>> {
    vec![
        rewrite!("neg_cancel"; "(+ ?a (- ?a))" => "zero"),
        rewrite!("div_cancel"; "(* ?a (/ ?a))" => "one"),

        rewrite!("double_neg"; "(- (- ?a)))" => "?a"),
        rewrite!("double_div"; "(/ (/ ?a)))" => "?a"),

        rewrite!("neg_def1"; "(- ?a)" => "(* ?a (- one))"),
        rewrite!("neg_def2"; "(* ?a (- one))" => "(- ?a)"),

        rewrite!("mul_neg";  "(* (- ?a) ?b)" => "(- (* ?a ?b))"),
        rewrite!("mul_neg_"; "(- (* ?a ?b))" => "(* (- ?a) ?b)"),

        rewrite!("neutral1";  "(/ one)" => "one"),
        rewrite!("neutral1_"; "one" => "(/ one)"),

        rewrite!("neutral2";  "(- zero)" => "zero"),
        rewrite!("neutral2_"; "zero" => "(- zero)"),

        rewrite!("flip";  "(- (/ ?a))" => "(/ (- ?a))"),
        rewrite!("flip_"; "(/ (- ?a))" => "(- (/ ?a))" ),

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

fn init_term2() -> String {
    use rand::{SeedableRng, rngs::StdRng};

    let mut rng = StdRng::from_seed([37u8; 32]);
    // let mut rng = rand::rng();

    let s = random_math(500, &mut rng).to_string();
    println!("{}", &s);
    s
}

pub fn run_ex1() {
    compare(&init_term2(), &rules(), 4);
}
