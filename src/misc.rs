use crate::*;

pub fn lookup_pat<L: Language>(pat: &PatternAst<L>, eg: &EGraph<L, ()>, subst: &Subst) -> Option<Id> {
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

pub fn pat_to_term<L: Language>(p: &PatternAst<L>, subst: &impl Fn(Var) -> RecExpr<L>) -> RecExpr<L> {
    subpat_to_term(Id::from(p.len() - 1), p, subst)
}

fn subpat_to_term<L: Language>(id: Id, p: &PatternAst<L>, subst: &impl Fn(Var) -> RecExpr<L>) -> RecExpr<L> {
    match &p[id] {
        ENodeOrVar::Var(v) => subst(*v),
        ENodeOrVar::ENode(n) => {
            n.join_recexprs(|i| subpat_to_term(i, p, subst))
        },
    }
}

