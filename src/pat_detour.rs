use crate::*;
use std::fmt::Display;

pub fn eqsat_pat_detour<L: Language + Display + FromOp>(init_term: &str, rws: &[Rewrite<L, ()>], stop_size: usize) {
    let st: RecExpr<L> = init_term.parse().unwrap();
    println!("Initial: {st}");
    let mut eg = EGraph::new(());
    let i = eg.add_expr(&st);

    eg.rebuild();
    for _ in 0..520 {
        pat_detour_eqsat_step(i, rws, &mut eg);

        let ex = Extractor::new(&eg, AstSize);
        let t = ex.find_best(i);
        println!("Detour Extracted: {}", t.1);
        println!("Total Size: {}", eg.total_size());
        if t.0 <= stop_size { break }
    }
}

pub fn pat_detour_eqsat_step<L: Language + Display>(root: Id, rws: &[Rewrite<L, ()>], eg: &mut EGraph<L, ()>) {
    let ex = Extractor::new(&eg, AstSize);
    let ctxt_cost = compute_ctxt_costs(root, eg, &ex);

    let mut matches: BTreeMap</*detour cost*/ usize, Vec<(/*rw id*/ usize, Id, Subst, /*ctxt_cost*/ usize, /*pat_cost*/ usize)>> = BTreeMap::default();
    for (rw_i, rw) in rws.iter().enumerate() {
        let lhs_pat = rw.searcher.get_pattern_ast().unwrap();
        let rhs_pat = rw.applier.get_pattern_ast().unwrap();

        for m in rw.searcher.search(eg) {
            let lhs = m.eclass;
            for subst in m.substs {
                let rhs = lookup_pat(&rhs_pat, eg, &subst);
                if Some(lhs) != rhs {
                    let pat_cost = pat_cost(lhs_pat, &subst, &ex);
                    // We don't subtract the root cost here, it's a constant offset, so why would we.
                    let cx_cost = ctxt_cost[&lhs];
                    let detour_cost = cx_cost + pat_cost;
                    if !matches.contains_key(&detour_cost) {
                        matches.insert(detour_cost, Vec::new());
                    }
                    matches.get_mut(&detour_cost).unwrap().push((rw_i, lhs, subst, cx_cost, pat_cost));
                }
            }
        }
    }

    let Some((full_cost, new_apps)) = matches.into_iter().next() else { return /*saturated*/ };

    let root_cost = ex.find_best_cost(root);
    for (rw_i, lhs, subst, cx_cost, pat_cost) in &new_apps {
        let rw = &rws[*rw_i];

        // Debugging info
        {
            println!("rule \"{}\": {} -> {}", rw.name, rw.searcher.get_pattern_ast().unwrap(), rw.applier.get_pattern_ast().unwrap());
            let ex = Extractor::new(&eg, AstSize);
            println!("cx_cost = {cx_cost}, pat_cost = {pat_cost}, full_cost = {full_cost}, root_cost = {root_cost}");
            for v in rw.searcher.vars() {
                let term = ex.find_best(subst[v]).1;
                println!("  {v} = {term}");
            }
            println!();
        }

        rw.applier.apply_one(eg, *lhs, subst, None, rw.name);
    }

    eg.rebuild();
}

fn pat_cost<L: Language>(pat: &PatternAst<L>, subst: &Subst, ex: &Extractor<AstSize, L, ()>) -> usize {
    let mut vec: Vec<usize> = Vec::new();
    for i in 0..pat.len() {
        let cost = match &pat[i.into()] {
            ENodeOrVar::ENode(n) => n.children().iter().map(|x| vec[usize::from(*x)]).sum::<usize>() + 1,
            ENodeOrVar::Var(v) => ex.find_best_cost(subst[*v]),
        };
        vec.push(cost);
    }
    vec.last().copied().unwrap()
}

