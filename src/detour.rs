use crate::*;

pub fn compute_detour_costs(id: Id, eg: &EG) -> BTreeMap<usize, Vec<Math>> {
    let ex = Extractor::new(eg, AstSize);
    let mut ctxt_cost = HashMap::new();

    // as this queue is a max-heap, we'll store usize::MAX - ctxt_cost in the usize of queue.
    let mut queue: BinaryHeap<(usize, Id)> = BinaryHeap::new();

    // initial
    queue.push((usize::MAX - 0, id));

    while let Some((cst, i)) = queue.pop() {
        let cst = usize::MAX - cst;
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
                queue.push((usize::MAX - ncst, c));
            }
        }
    }

    let mut dd: BTreeMap<usize, Vec<Math>> = Default::default();
    let opt_cost = ex.find_best_cost(id);
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

    dd
}
