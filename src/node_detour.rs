use crate::*;
use std::fmt::Display;

pub fn eqsat_node_detour<L: Language + Display + FromOp>(init_term: &str, rws: &[Rewrite<L, ()>], stop_size: usize) {
    let st: RecExpr<L> = init_term.parse().unwrap();
    println!("Initial: {st}");
    let mut eg = EGraph::new(());
    let i = eg.add_expr(&st);

    eg.rebuild();
    for _ in 0..70 {
        node_detour_eqsat_step(i, rws, &mut eg);

        let ex = Extractor::new(&eg, AstSize);
        let t = ex.find_best(i);
        println!("Detour Extracted: {}", t.1);
        println!("Total Size: {}", eg.total_size());
        if t.0 <= stop_size { break }
    }
}

// one iteration of eqsat governed by the detour system.
pub fn node_detour_eqsat_step<L: Language + Display>(root: Id, rws: &[Rewrite<L, ()>], eg: &mut EGraph<L, ()>) {
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

fn compute_detour_costs<L: Language>(root: Id, eg: &EGraph<L, ()>) -> (Extractor<AstSize, L, ()>, HashMap<Id, usize>, BTreeMap<usize, Vec<L>>) {
    let ex = Extractor::new(eg, AstSize);
    let ctxt_cost = compute_ctxt_costs(root, eg, &ex);

    let mut dd: BTreeMap<usize, Vec<L>> = Default::default();
    let opt_cost = ex.find_best_cost(root);
    for cc in eg.classes() {
        for n in &eg[cc.id].nodes {
            let cl = eg.lookup(&mut n.clone()).unwrap();
            let class_ctxt_cost = ctxt_cost[&cl];
            let node_cost = AstSize.cost(n, |k| ex.find_best_cost(k));
            let det = class_ctxt_cost + node_cost - opt_cost;
            if !dd.contains_key(&det) {
                dd.insert(det, Vec::new());
            }
            dd.get_mut(&det).unwrap().push(n.clone());
        }
    }

    (ex, ctxt_cost, dd)
}

