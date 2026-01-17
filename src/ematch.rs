use crate::*;

pub fn ematch_node<L: Language>(pat: &PatternAst<L>, n: &L, eg: &EGraph<L, ()>) -> Vec<Subst> {
    match &pat.last().unwrap() {
        ENodeOrVar::Var(v) => {
            let mut subst = Subst::default();
            let cl = eg.lookup(&mut n.clone()).unwrap();
            subst.insert(*v, cl);
            vec![subst]
        },
        ENodeOrVar::ENode(pn) => {
            if !n.matches(&pn) {
                return Vec::new();
            }

            let mut accum = vec![Subst::default()];
            for (pc, c) in pn.children().iter().zip(n.children().iter()) {
                for a in std::mem::take(&mut accum) {
                    let tt = ematch_impl(*pc, pat, *c, eg, a);
                    accum.extend(tt);
                }
            }
            accum
        },
    }
}

pub fn ematch_impl<L: Language>(pat_id: Id, pat: &PatternAst<L>, class: Id, eg: &EGraph<L, ()>, subst: Subst) -> Vec<Subst> {
    match &pat[pat_id] {
        ENodeOrVar::Var(v) => {
            let mut subst = subst;
            if let Some(x) = subst.get(*v) {
                if *x != class { return Vec::new() }
            } else {
                subst.insert(*v, class);
            }
            vec![subst]
        },
        ENodeOrVar::ENode(pn) => {
            let mut out = Vec::new();
            for n in &eg[class].nodes {
                if !n.matches(&pn) { continue }

                let mut accum = vec![subst.clone()];
                for (pc, c) in pn.children().iter().zip(n.children().iter()) {
                    for a in std::mem::take(&mut accum) {
                        let tt = ematch_impl(*pc, pat, *c, eg, a);
                        accum.extend(tt);
                    }
                }
                out.extend(accum);
            }
            out
        },
    }
}
