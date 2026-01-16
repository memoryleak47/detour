use crate::*;

pub fn ematch_node(pat: &PatternAst<Math>, n: &Math, eg: &EG) -> Vec<Subst> {
    match &pat.last().unwrap() {
        ENodeOrVar::Var(v) => {
            todo!()
        },
        ENodeOrVar::ENode(pn) => {
            if n.discriminant() != pn.discriminant() {
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

pub fn ematch_impl(pat_id: Id, pat: &PatternAst<Math>, class: Id, eg: &EG, subst: Subst) -> Vec<Subst> {
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
                if n.discriminant() != pn.discriminant() { continue }

                let mut accum = vec![subst.clone()];
                for (pc, c) in pn.children().iter().zip(n.children().iter()) {
                    for a in std::mem::take(&mut accum) {
                        accum.extend(ematch_impl(*pc, pat, *c, eg, a));
                    }
                }
                out.extend(accum);
            }
            out
        },
    }
}
