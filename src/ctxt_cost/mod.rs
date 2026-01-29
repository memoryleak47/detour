use crate::*;

mod minqueue;
use minqueue::*;

pub fn compute_ctxt_costs<L: Language>(root: Id, eg: &EGraph<L, ()>, ex: &Extractor<AstSize, L, ()>) -> HashMap<Id, usize> {
    let mut ctxt_cost = HashMap::new();

    let mut queue: MinPrioQueue<usize, Id> = MinPrioQueue::new();

    // initial
    queue.push(0, root);

    while let Some((cst, i)) = queue.pop() {
        if ctxt_cost.contains_key(&i) { continue }
        ctxt_cost.insert(i, cst);
        for e in &eg[i].nodes {
            let e_cost = AstSize.cost(e, |k| ex.find_best_cost(k));
            for &c in e.children() {
                // optimization: don't push junk to the queue.
                // NOTE: if we remembered what's the best thing we already pushed to the queue for some class,
                // we could do more efficient pruning.
                if ctxt_cost.contains_key(&c) { continue }

                let c_cost = ex.find_best_cost(c);
                let ncst = e_cost + cst - c_cost;
                queue.push(ncst, c);
            }
        }
    }

    ctxt_cost
}


