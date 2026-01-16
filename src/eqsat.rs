use crate::*;

// one iteration of eqsat governed by the detour system.
pub fn detour_eqsat_iter(id: Id, rws: &[Rewrite<Math, ()>], eg: &mut EG) {
    let dd = compute_detour_costs(id, eg);

    let mut new_apps: Vec<(/*rw index*/ usize, /*lhs*/ Id, Subst)> = Vec::new();

    for (_, x) in &dd {
        for n in x {
            let lhs = eg.lookup(&mut n.clone()).unwrap();
            for (rw_i, rw) in rws.iter().enumerate() {
                let lhs_pat = rw.searcher.get_pattern_ast().unwrap();
                let rhs_pat = rw.applier.get_pattern_ast().unwrap();
                for subst in ematch_node(lhs_pat, n, eg) {
                    let rhs = lookup_pat(&rhs_pat, eg, &subst);
                    if Some(lhs) != rhs {
                        new_apps.push((rw_i, lhs, subst));
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
