use crate::*;
use std::fmt::Display;

fn pat_to_term<L: Language>(p: &PatternAst<L>, subst: &impl Fn(Var) -> RecExpr<L>) -> RecExpr<L> {
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

// one iteration of eqsat governed by the detour system.
pub fn detour_eqsat_iter<L: Language + Display>(root: Id, rws: &[Rewrite<L, ()>], eg: &mut EGraph<L, ()>) {
    let (ex, ctxt_cost, dd) = compute_detour_costs(root, eg);

    let mut new_apps: Vec<(/*rw index*/ usize, /*lhs*/ Id, Subst)> = Vec::new();

    let root_ex_cost = ex.find_best_cost(root);
    for (cst, x) in &dd {
        for n in x {
            let lhs = eg.lookup(&mut n.clone()).unwrap();
            for (rw_i, rw) in rws.iter().enumerate() {
                let lhs_pat = rw.searcher.get_pattern_ast().unwrap();
                let rhs_pat = rw.applier.get_pattern_ast().unwrap();
                for subst in ematch_node(lhs_pat, n, eg) {
                    let rhs = lookup_pat(&rhs_pat, eg, &subst);
                    if Some(lhs) != rhs {
                        {
                            println!("=====================================================================================================");
                            println!();
                            println!();
                            let ex = Extractor::new(&eg, AstSize);
                            // this prints the equations we have learned:
                            let subst_f = |v| ex.find_best(subst[v]).1;
                            let lhs_vars = rw.searcher.vars();
                            println!("    rule: {}", rw.name);
                            for v in lhs_vars {
                                println!("--- var({v}) = {}", ex.find_best(subst[v]).1);
                            }
                            let lhs_t = pat_to_term(lhs_pat, &subst_f);
                            let rhs_t = pat_to_term(rhs_pat, &subst_f);
                            let node_cost = AstSize.cost(n, |k| ex.find_best_cost(k));

                            let lhs_ctxt_cost = ctxt_cost[&lhs];
                            assert!(*cst == lhs_ctxt_cost + node_cost - root_ex_cost);
                            println!("    class ctxt cost: {lhs_ctxt_cost}");
                            println!("    root extract cost: {root_ex_cost}");
                            println!("    node extract cost: {node_cost}");
                            println!("    -> e-node detour cost: {cst}");
                            println!();
                            println!("> {lhs_t}");
                            println!();
                            println!("= {rhs_t};");
                            println!();
                        }
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

fn lookup_pat<L: Language>(pat: &PatternAst<L>, eg: &EGraph<L, ()>, subst: &Subst) -> Option<Id> {
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
