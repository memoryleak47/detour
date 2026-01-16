use crate::*;

pub fn compute_detour_costs(id: Id, eg: &EG) -> BTreeMap<usize, Vec<Id>> {
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
                let c_cost = ex.find_best_cost(c);
                let ncst = e_cost + cst - c_cost;
                queue.push((usize::MAX - ncst, c));
            }
        }
    }

    let mut dd: BTreeMap<usize, Vec<Id>> = Default::default();
    let opt_cost = ex.find_best_cost(id);
    for x in eg.classes() {
        let x = x.id;
        let det = ctxt_cost[&x] + ex.find_best_cost(x) - opt_cost;
        if !dd.contains_key(&det) {
            dd.insert(det, Vec::new());
        }
        dd.get_mut(&det).unwrap().push(x);
    }

    /*
        println!("===============");
        for (cst, xx) in dd.iter() {
            dbg!(cst);
            for x in xx {
                println!("{}", ex.find_best(*x).1);
            }
        }
        println!("===============");
    */

    dd
}
