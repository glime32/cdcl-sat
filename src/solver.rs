// Solveur CDCL : propagation avec deux littéraux surveillés, apprentissage
// de clauses (1-UIP), heuristique VSIDS, sauvegarde de phase, redémarrages
// de Luby et nettoyage des clauses apprises selon leur LBD.

pub type Lit = u32; // 2*var pour x, 2*var+1 pour ¬x

#[inline]
pub fn var(l: Lit) -> usize {
    (l >> 1) as usize
}
#[inline]
pub fn neg(l: Lit) -> Lit {
    l ^ 1
}
pub fn from_dimacs(x: i32) -> Lit {
    let v = (x.unsigned_abs() - 1) << 1;
    if x < 0 { v | 1 } else { v }
}
pub fn to_dimacs(l: Lit) -> i32 {
    let v = (var(l) + 1) as i32;
    if l & 1 == 1 { -v } else { v }
}

#[derive(Clone, Copy, PartialEq, Debug)]
enum Val {
    Undef,
    True,
    False,
}

struct Clause {
    lits: Vec<Lit>,
    learnt: bool,
    deleted: bool,
    lbd: u32,
    activity: f64,
}

#[derive(Clone, Copy)]
struct Watch {
    cref: u32,
    blocker: Lit,
}

#[derive(Default, Debug, Clone)]
pub struct Stats {
    pub decisions: u64,
    pub propagations: u64,
    pub conflicts: u64,
    pub restarts: u64,
    pub learnt: u64,
    pub deleted: u64,
}

pub enum Outcome {
    Sat(Vec<bool>),
    Unsat,
    Unknown,
}

pub struct Solver {
    nvars: usize,
    clauses: Vec<Clause>,
    watches: Vec<Vec<Watch>>,
    assign: Vec<Val>,
    level: Vec<u32>,
    reason: Vec<Option<u32>>,
    trail: Vec<Lit>,
    trail_lim: Vec<usize>,
    qhead: usize,
    activity: Vec<f64>,
    var_inc: f64,
    cla_inc: f64,
    heap: Heap,
    phase: Vec<bool>,
    seen: Vec<bool>,
    unsat: bool,
    pub stats: Stats,
    pub max_conflicts: Option<u64>,
}

impl Solver {
    pub fn new(nvars: usize) -> Solver {
        let mut s = Solver {
            nvars,
            clauses: Vec::new(),
            watches: vec![Vec::new(); 2 * nvars],
            assign: vec![Val::Undef; nvars],
            level: vec![0; nvars],
            reason: vec![None; nvars],
            trail: Vec::with_capacity(nvars),
            trail_lim: Vec::new(),
            qhead: 0,
            activity: vec![0.0; nvars],
            var_inc: 1.0,
            cla_inc: 1.0,
            heap: Heap::new(nvars),
            phase: vec![false; nvars],
            seen: vec![false; nvars],
            unsat: false,
            stats: Stats::default(),
            max_conflicts: None,
        };
        for v in 0..nvars {
            s.heap.insert(v, &s.activity);
        }
        s
    }

    fn value(&self, l: Lit) -> Val {
        match self.assign[var(l)] {
            Val::Undef => Val::Undef,
            Val::True => if l & 1 == 0 { Val::True } else { Val::False },
            Val::False => if l & 1 == 0 { Val::False } else { Val::True },
        }
    }

    fn decision_level(&self) -> u32 {
        self.trail_lim.len() as u32
    }

    /// Ajoute une clause du problème (avant la résolution).
    pub fn add_clause(&mut self, lits: &[Lit]) {
        if self.unsat {
            return;
        }
        let mut c: Vec<Lit> = lits.to_vec();
        c.sort_unstable();
        c.dedup();
        if c.windows(2).any(|w| w[0] == neg(w[1])) {
            return; // x ∨ ¬x : toujours vraie
        }
        c.retain(|&l| self.value(l) != Val::False);
        if c.iter().any(|&l| self.value(l) == Val::True) {
            return;
        }
        match c.len() {
            0 => self.unsat = true,
            1 => {
                self.enqueue(c[0], None);
                if self.propagate().is_some() {
                    self.unsat = true;
                }
            }
            _ => {
                self.attach(c, false, 0);
            }
        }
    }

    fn attach(&mut self, lits: Vec<Lit>, learnt: bool, lbd: u32) -> u32 {
        let cref = self.clauses.len() as u32;
        self.watches[lits[0] as usize].push(Watch { cref, blocker: lits[1] });
        self.watches[lits[1] as usize].push(Watch { cref, blocker: lits[0] });
        self.clauses.push(Clause { lits, learnt, deleted: false, lbd, activity: 0.0 });
        cref
    }

    fn enqueue(&mut self, l: Lit, reason: Option<u32>) {
        let v = var(l);
        self.assign[v] = if l & 1 == 0 { Val::True } else { Val::False };
        self.level[v] = self.decision_level();
        self.reason[v] = reason;
        self.trail.push(l);
    }

    /// Propagation unitaire. watches[l] contient les clauses qui surveillent l :
    /// quand l devient faux, il faut leur trouver un autre littéral non faux.
    fn propagate(&mut self) -> Option<u32> {
        let mut conflict = None;
        while self.qhead < self.trail.len() && conflict.is_none() {
            let p = self.trail[self.qhead];
            self.qhead += 1;
            self.stats.propagations += 1;
            let false_lit = neg(p);
            let mut ws = std::mem::take(&mut self.watches[false_lit as usize]);
            let (mut i, mut j) = (0, 0);
            while i < ws.len() {
                let w = ws[i];
                i += 1;
                if self.value(w.blocker) == Val::True {
                    ws[j] = w;
                    j += 1;
                    continue;
                }
                let cref = w.cref as usize;
                if self.clauses[cref].deleted {
                    continue;
                }
                {
                    let c = &mut self.clauses[cref].lits;
                    if c[0] == false_lit {
                        c.swap(0, 1);
                    }
                }
                let first = self.clauses[cref].lits[0];
                if first != w.blocker && self.value(first) == Val::True {
                    ws[j] = Watch { cref: w.cref, blocker: first };
                    j += 1;
                    continue;
                }
                let mut moved = false;
                let n = self.clauses[cref].lits.len();
                for k in 2..n {
                    let l = self.clauses[cref].lits[k];
                    if self.value(l) != Val::False {
                        self.clauses[cref].lits.swap(1, k);
                        self.watches[l as usize].push(Watch { cref: w.cref, blocker: first });
                        moved = true;
                        break;
                    }
                }
                if moved {
                    continue;
                }
                ws[j] = Watch { cref: w.cref, blocker: first };
                j += 1;
                if self.value(first) == Val::False {
                    conflict = Some(w.cref);
                    while i < ws.len() {
                        ws[j] = ws[i];
                        j += 1;
                        i += 1;
                    }
                } else {
                    self.enqueue(first, Some(w.cref));
                }
            }
            ws.truncate(j);
            self.watches[false_lit as usize] = ws;
        }
        conflict
    }

    fn bump_var(&mut self, v: usize) {
        self.activity[v] += self.var_inc;
        if self.activity[v] > 1e100 {
            for a in self.activity.iter_mut() {
                *a *= 1e-100;
            }
            self.var_inc *= 1e-100;
        }
        self.heap.increase(v, &self.activity);
    }

    fn bump_clause(&mut self, cref: usize) {
        let c = &mut self.clauses[cref];
        c.activity += self.cla_inc;
        if c.activity > 1e20 {
            for c in self.clauses.iter_mut().filter(|c| c.learnt) {
                c.activity *= 1e-20;
            }
            self.cla_inc *= 1e-20;
        }
    }

    /// Analyse du conflit : on remonte les raisons depuis la clause en conflit
    /// jusqu'au premier point d'implication unique (1-UIP) du dernier niveau.
    fn analyze(&mut self, mut confl: u32) -> (Vec<Lit>, u32) {
        let mut learnt: Vec<Lit> = vec![0];
        let mut path = 0;
        let mut p: Option<Lit> = None;
        let mut index = self.trail.len();
        loop {
            if self.clauses[confl as usize].learnt {
                self.bump_clause(confl as usize);
            }
            let start = if p.is_some() { 1 } else { 0 };
            let n = self.clauses[confl as usize].lits.len();
            for k in start..n {
                let q = self.clauses[confl as usize].lits[k];
                let v = var(q);
                if !self.seen[v] && self.level[v] > 0 {
                    self.seen[v] = true;
                    self.bump_var(v);
                    if self.level[v] >= self.decision_level() {
                        path += 1;
                    } else {
                        learnt.push(q);
                    }
                }
            }
            loop {
                index -= 1;
                if self.seen[var(self.trail[index])] {
                    break;
                }
            }
            let lit = self.trail[index];
            self.seen[var(lit)] = false;
            path -= 1;
            p = Some(lit);
            if path == 0 {
                break;
            }
            confl = self.reason[var(lit)].expect("littéral impliqué sans raison");
        }
        learnt[0] = neg(p.unwrap());

        // minimisation : un littéral est inutile si sa raison ne contient que
        // des littéraux déjà dans la clause (ou fixés au niveau 0)
        let keep: Vec<bool> = learnt
            .iter()
            .enumerate()
            .map(|(k, &l)| {
                if k == 0 {
                    return true;
                }
                match self.reason[var(l)] {
                    None => true,
                    Some(r) => self.clauses[r as usize].lits[1..]
                        .iter()
                        .any(|&q| !self.seen[var(q)] && self.level[var(q)] > 0),
                }
            })
            .collect();
        for &l in &learnt[1..] {
            self.seen[var(l)] = false;
        }
        let mut learnt: Vec<Lit> = learnt.into_iter().zip(keep).filter(|&(_, k)| k).map(|(l, _)| l).collect();

        // niveau de retour : le plus haut niveau parmi les autres littéraux,
        // qu'on place en position 1 pour qu'il soit surveillé
        let mut back = 0;
        if learnt.len() > 1 {
            let mut best = 1;
            for k in 2..learnt.len() {
                if self.level[var(learnt[k])] > self.level[var(learnt[best])] {
                    best = k;
                }
            }
            learnt.swap(1, best);
            back = self.level[var(learnt[1])];
        }
        (learnt, back)
    }

    fn lbd(&self, lits: &[Lit]) -> u32 {
        let mut levels: Vec<u32> = lits.iter().map(|&l| self.level[var(l)]).collect();
        levels.sort_unstable();
        levels.dedup();
        levels.len() as u32
    }

    fn cancel_until(&mut self, lvl: u32) {
        if self.decision_level() <= lvl {
            return;
        }
        let lim = self.trail_lim[lvl as usize];
        for k in (lim..self.trail.len()).rev() {
            let l = self.trail[k];
            let v = var(l);
            self.phase[v] = l & 1 == 0;
            self.assign[v] = Val::Undef;
            self.reason[v] = None;
            if !self.heap.contains(v) {
                self.heap.insert(v, &self.activity);
            }
        }
        self.trail.truncate(lim);
        self.trail_lim.truncate(lvl as usize);
        self.qhead = lim;
    }

    fn pick_branch(&mut self) -> Option<Lit> {
        while let Some(v) = self.heap.pop(&self.activity) {
            if self.assign[v] == Val::Undef {
                let l = (v as Lit) << 1;
                return Some(if self.phase[v] { l } else { l | 1 });
            }
        }
        None
    }

    fn locked(&self, cref: usize) -> bool {
        let l = self.clauses[cref].lits[0];
        self.value(l) == Val::True && self.reason[var(l)] == Some(cref as u32)
    }

    /// Garde la moitié la plus utile des clauses apprises : petite LBD d'abord
    /// (les clauses « glue » de LBD ≤ 2 ne sont jamais jetées), puis activité.
    fn reduce_db(&mut self) {
        let mut cand: Vec<usize> = (0..self.clauses.len())
            .filter(|&i| {
                let c = &self.clauses[i];
                c.learnt && !c.deleted && c.lbd > 2 && !self.locked(i)
            })
            .collect();
        cand.sort_by(|&a, &b| {
            let (ca, cb) = (&self.clauses[a], &self.clauses[b]);
            cb.lbd.cmp(&ca.lbd).then(ca.activity.partial_cmp(&cb.activity).unwrap())
        });
        for &i in &cand[..cand.len() / 2] {
            self.clauses[i].deleted = true;
            self.clauses[i].lits = Vec::new();
            self.stats.deleted += 1;
        }
    }

    pub fn solve(&mut self) -> Outcome {
        if self.unsat {
            return Outcome::Unsat;
        }
        if self.propagate().is_some() {
            return Outcome::Unsat;
        }
        let mut restart_idx = 0;
        let mut next_reduce = 2000u64;
        loop {
            let budget = 100 * luby(restart_idx);
            restart_idx += 1;
            let mut conflicts_here = 0;
            loop {
                if let Some(confl) = self.propagate() {
                    self.stats.conflicts += 1;
                    conflicts_here += 1;
                    if self.decision_level() == 0 {
                        return Outcome::Unsat;
                    }
                    let (learnt, back) = self.analyze(confl);
                    self.cancel_until(back);
                    if learnt.len() == 1 {
                        self.enqueue(learnt[0], None);
                    } else {
                        let lbd = self.lbd(&learnt);
                        let first = learnt[0];
                        let cref = self.attach(learnt, true, lbd);
                        self.bump_clause(cref as usize);
                        self.enqueue(first, Some(cref));
                    }
                    self.stats.learnt += 1;
                    self.var_inc /= 0.95;
                    self.cla_inc /= 0.999;
                    if let Some(m) = self.max_conflicts {
                        if self.stats.conflicts >= m {
                            return Outcome::Unknown;
                        }
                    }
                } else {
                    if conflicts_here >= budget {
                        self.stats.restarts += 1;
                        self.cancel_until(0);
                        break;
                    }
                    if self.stats.conflicts >= next_reduce {
                        next_reduce = self.stats.conflicts + 2000 + 300 * self.stats.restarts;
                        self.reduce_db();
                    }
                    match self.pick_branch() {
                        None => {
                            let model = (0..self.nvars).map(|v| self.assign[v] == Val::True).collect();
                            return Outcome::Sat(model);
                        }
                        Some(l) => {
                            self.stats.decisions += 1;
                            self.trail_lim.push(self.trail.len());
                            self.enqueue(l, None);
                        }
                    }
                }
            }
        }
    }
}

/// Suite de Luby : 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8 ...
fn luby(i: u64) -> u64 {
    let mut i = i + 1;
    loop {
        let k = 64 - i.leading_zeros() as u64; // 2^(k-1) <= i < 2^k
        if i == (1 << k) - 1 {
            return 1 << (k - 1);
        }
        i -= (1 << (k - 1)) - 1;
    }
}

// Tas binaire indexé : la variable la plus active en tête.
struct Heap {
    data: Vec<usize>,
    pos: Vec<Option<usize>>,
}

impl Heap {
    fn new(n: usize) -> Heap {
        Heap { data: Vec::with_capacity(n), pos: vec![None; n] }
    }
    fn contains(&self, v: usize) -> bool {
        self.pos[v].is_some()
    }
    fn insert(&mut self, v: usize, act: &[f64]) {
        self.pos[v] = Some(self.data.len());
        self.data.push(v);
        self.up(self.data.len() - 1, act);
    }
    fn increase(&mut self, v: usize, act: &[f64]) {
        if let Some(i) = self.pos[v] {
            self.up(i, act);
        }
    }
    fn pop(&mut self, act: &[f64]) -> Option<usize> {
        if self.data.is_empty() {
            return None;
        }
        let top = self.data.swap_remove(0);
        self.pos[top] = None;
        if !self.data.is_empty() {
            self.pos[self.data[0]] = Some(0);
            self.down(0, act);
        }
        Some(top)
    }
    fn up(&mut self, mut i: usize, act: &[f64]) {
        let v = self.data[i];
        while i > 0 {
            let parent = (i - 1) / 2;
            if act[self.data[parent]] >= act[v] {
                break;
            }
            self.data[i] = self.data[parent];
            self.pos[self.data[i]] = Some(i);
            i = parent;
        }
        self.data[i] = v;
        self.pos[v] = Some(i);
    }
    fn down(&mut self, mut i: usize, act: &[f64]) {
        let v = self.data[i];
        let n = self.data.len();
        loop {
            let mut child = 2 * i + 1;
            if child >= n {
                break;
            }
            if child + 1 < n && act[self.data[child + 1]] > act[self.data[child]] {
                child += 1;
            }
            if act[self.data[child]] <= act[v] {
                break;
            }
            self.data[i] = self.data[child];
            self.pos[self.data[i]] = Some(i);
            i = child;
        }
        self.data[i] = v;
        self.pos[v] = Some(i);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn luby_sequence() {
        let v: Vec<u64> = (0..15).map(luby).collect();
        assert_eq!(v, vec![1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8]);
    }

    fn brute_force(n: usize, clauses: &[Vec<i32>]) -> bool {
        (0..1u32 << n).any(|m| {
            clauses.iter().all(|c| c.iter().any(|&x| ((m >> (x.unsigned_abs() - 1)) & 1 == 1) == (x > 0)))
        })
    }

    #[test]
    fn agrees_with_brute_force() {
        let mut seed = 12345u64;
        let mut rnd = |m: u64| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed % m
        };
        for _ in 0..3000 {
            let n = 1 + rnd(12) as usize;
            let m = rnd(60) as usize;
            let clauses: Vec<Vec<i32>> = (0..m)
                .map(|_| {
                    let k = 1 + rnd(4) as usize;
                    (0..k).map(|_| {
                        let v = 1 + rnd(n as u64) as i32;
                        if rnd(2) == 0 { v } else { -v }
                    }).collect()
                })
                .collect();
            let mut s = Solver::new(n);
            for c in &clauses {
                s.add_clause(&c.iter().map(|&x| from_dimacs(x)).collect::<Vec<_>>());
            }
            let expected = brute_force(n, &clauses);
            match s.solve() {
                Outcome::Sat(model) => {
                    assert!(expected, "SAT annoncé à tort");
                    for c in &clauses {
                        assert!(c.iter().any(|&x| model[(x.unsigned_abs() - 1) as usize] == (x > 0)), "modèle faux");
                    }
                }
                Outcome::Unsat => assert!(!expected, "UNSAT annoncé à tort"),
                Outcome::Unknown => unreachable!(),
            }
        }
    }
}
