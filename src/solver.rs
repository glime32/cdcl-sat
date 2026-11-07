// Solveur CDCL : propagation avec deux littéraux surveillés, apprentissage
// de clauses (1-UIP) avec minimisation, heuristique VSIDS, sauvegarde de
// phase, redémarrages de Luby et nettoyage des clauses apprises selon leur LBD.
//
// Toutes les clauses vivent dans un seul Vec<u32> (l'« arène ») : une clause
// = 2 mots d'en-tête puis ses littéraux. Une référence de clause est l'indice
// de son en-tête. C'est beaucoup plus rapide qu'un Vec par clause, parce que
// la propagation passe son temps à sauter d'une clause à l'autre.

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

const TRUE: i8 = 1;
const FALSE: i8 = -1;
const UNDEF: i8 = 0;

// en-tête : [taille | appris << 31 | supprimé << 30] [lbd]
const HEADER: usize = 2;
const LEARNT: u32 = 1 << 31;
const DELETED: u32 = 1 << 30;
const SIZE_MASK: u32 = (1 << 30) - 1;
const NO_REASON: u32 = u32::MAX;

#[derive(Clone, Copy)]
struct Watch {
    cref: u32,
    blocker: Lit,
    binary: bool, // clause à 2 littéraux : le « bloqueur » est l'autre littéral
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
    arena: Vec<u32>,
    wasted: usize,
    learnts: Vec<u32>,
    watches: Vec<Vec<Watch>>,
    values: Vec<i8>, // indexé par littéral
    level: Vec<u32>,
    reason: Vec<u32>,
    trail: Vec<Lit>,
    trail_lim: Vec<usize>,
    qhead: usize,
    activity: Vec<f64>,
    var_inc: f64,
    heap: Heap,
    phase: Vec<bool>,
    seen: Vec<bool>,
    stack: Vec<Lit>,
    to_clear: Vec<usize>,
    unsat: bool,
    pub stats: Stats,
    pub max_conflicts: Option<u64>,
}

impl Solver {
    pub fn new(nvars: usize) -> Solver {
        let mut s = Solver {
            nvars,
            arena: Vec::new(),
            wasted: 0,
            learnts: Vec::new(),
            watches: vec![Vec::new(); 2 * nvars],
            values: vec![UNDEF; 2 * nvars],
            level: vec![0; nvars],
            reason: vec![NO_REASON; nvars],
            trail: Vec::with_capacity(nvars),
            trail_lim: Vec::new(),
            qhead: 0,
            activity: vec![0.0; nvars],
            var_inc: 1.0,
            heap: Heap::new(nvars),
            phase: vec![false; nvars],
            seen: vec![false; nvars],
            stack: Vec::new(),
            to_clear: Vec::new(),
            unsat: false,
            stats: Stats::default(),
            max_conflicts: None,
        };
        for v in 0..nvars {
            s.heap.insert(v, &s.activity);
        }
        s
    }

    #[inline]
    fn size(&self, c: u32) -> usize {
        (self.arena[c as usize] & SIZE_MASK) as usize
    }
    #[inline]
    fn lits(&self, c: u32) -> &[Lit] {
        let start = c as usize + HEADER;
        &self.arena[start..start + self.size(c)]
    }
    #[inline]
    fn value(&self, l: Lit) -> i8 {
        self.values[l as usize]
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
        if c.iter().any(|&l| self.value(l) == TRUE) {
            return;
        }
        c.retain(|&l| self.value(l) != FALSE);
        match c.len() {
            0 => self.unsat = true,
            1 => {
                self.enqueue(c[0], NO_REASON);
                if self.propagate().is_some() {
                    self.unsat = true;
                }
            }
            _ => {
                self.attach(&c, false, 0);
            }
        }
    }

    fn attach(&mut self, lits: &[Lit], learnt: bool, lbd: u32) -> u32 {
        let cref = self.arena.len() as u32;
        self.arena.push(lits.len() as u32 | if learnt { LEARNT } else { 0 });
        self.arena.push(lbd);
        self.arena.extend_from_slice(lits);
        let binary = lits.len() == 2;
        self.watches[lits[0] as usize].push(Watch { cref, blocker: lits[1], binary });
        self.watches[lits[1] as usize].push(Watch { cref, blocker: lits[0], binary });
        if learnt {
            self.learnts.push(cref);
        }
        cref
    }

    #[inline]
    fn enqueue(&mut self, l: Lit, reason: u32) {
        let v = var(l);
        self.values[l as usize] = TRUE;
        self.values[neg(l) as usize] = FALSE;
        self.level[v] = self.decision_level();
        self.reason[v] = reason;
        self.trail.push(l);
    }

    /// Propagation unitaire. watches[l] contient les clauses qui surveillent l :
    /// quand l devient faux, il faut leur trouver un autre littéral non faux.
    fn propagate(&mut self) -> Option<u32> {
        while self.qhead < self.trail.len() {
            let p = self.trail[self.qhead];
            self.qhead += 1;
            self.stats.propagations += 1;
            let false_lit = neg(p);
            let mut ws = std::mem::take(&mut self.watches[false_lit as usize]);
            let (mut i, mut j) = (0, 0);
            let n = ws.len();
            let mut conflict = None;
            'watches: while i < n {
                let w = ws[i];
                i += 1;
                let bv = self.values[w.blocker as usize];
                if bv == TRUE {
                    ws[j] = w;
                    j += 1;
                    continue;
                }
                if w.binary {
                    // pas besoin de lire la clause : l'autre littéral est le bloqueur
                    let c = w.cref as usize;
                    if self.arena[c] & DELETED != 0 {
                        continue;
                    }
                    ws[j] = w;
                    j += 1;
                    if bv == FALSE {
                        conflict = Some(w.cref);
                        while i < n {
                            ws[j] = ws[i];
                            j += 1;
                            i += 1;
                        }
                    } else {
                        if self.arena[c + HEADER] != w.blocker {
                            self.arena.swap(c + HEADER, c + HEADER + 1); // le littéral impliqué en tête
                        }
                        self.enqueue(w.blocker, w.cref);
                    }
                    continue;
                }
                let c = w.cref as usize;
                let head = self.arena[c];
                if head & DELETED != 0 {
                    continue;
                }
                let size = (head & SIZE_MASK) as usize;
                let lits = c + HEADER;
                if self.arena[lits] == false_lit {
                    self.arena.swap(lits, lits + 1);
                }
                let first = self.arena[lits];
                let w2 = Watch { cref: w.cref, blocker: first, binary: false };
                if first != w.blocker && self.values[first as usize] == TRUE {
                    ws[j] = w2;
                    j += 1;
                    continue;
                }
                for k in 2..size {
                    let l = self.arena[lits + k];
                    if self.values[l as usize] != FALSE {
                        self.arena.swap(lits + 1, lits + k);
                        self.watches[l as usize].push(w2);
                        continue 'watches;
                    }
                }
                ws[j] = w2;
                j += 1;
                if self.values[first as usize] == FALSE {
                    conflict = Some(w.cref);
                    while i < n {
                        ws[j] = ws[i];
                        j += 1;
                        i += 1;
                    }
                } else {
                    self.enqueue(first, w.cref);
                }
            }
            ws.truncate(j);
            self.watches[false_lit as usize] = ws;
            if conflict.is_some() {
                return conflict;
            }
        }
        None
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

    /// Analyse du conflit : on remonte les raisons depuis la clause en conflit
    /// jusqu'au premier point d'implication unique (1-UIP) du dernier niveau.
    fn analyze(&mut self, mut confl: u32, learnt: &mut Vec<Lit>) -> u32 {
        learnt.clear();
        learnt.push(0);
        let mut path = 0;
        let mut p: Option<Lit> = None;
        let mut index = self.trail.len();
        let dl = self.decision_level();
        loop {
            let size = self.size(confl);
            let start = confl as usize + HEADER + if p.is_some() { 1 } else { 0 };
            for k in start..confl as usize + HEADER + size {
                let q = self.arena[k];
                let v = var(q);
                if !self.seen[v] && self.level[v] > 0 {
                    self.seen[v] = true;
                    self.bump_var(v);
                    if self.level[v] >= dl {
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
            confl = self.reason[var(lit)];
        }
        learnt[0] = neg(p.unwrap());

        // minimisation récursive : un littéral est inutile si tout ce qui l'a
        // impliqué est déjà dans la clause (directement ou de proche en proche)
        self.to_clear.clear();
        self.to_clear.extend(learnt[1..].iter().map(|&l| var(l)));
        let mut levels = 0u64;
        for &l in &learnt[1..] {
            levels |= 1 << (self.level[var(l)] & 63);
        }
        let mut kept = 1;
        for k in 1..learnt.len() {
            let l = learnt[k];
            if self.reason[var(l)] == NO_REASON || !self.redundant(l, levels) {
                learnt[kept] = l;
                kept += 1;
            }
        }
        learnt.truncate(kept);
        for &v in &self.to_clear {
            self.seen[v] = false;
        }

        // niveau de retour : le plus haut parmi les autres littéraux, placé en 1
        if learnt.len() == 1 {
            return 0;
        }
        let mut best = 1;
        for k in 2..learnt.len() {
            if self.level[var(learnt[k])] > self.level[var(learnt[best])] {
                best = k;
            }
        }
        learnt.swap(1, best);
        self.level[var(learnt[1])]
    }

    fn redundant(&mut self, l: Lit, levels: u64) -> bool {
        self.stack.clear();
        self.stack.push(l);
        let top = self.to_clear.len();
        while let Some(x) = self.stack.pop() {
            let r = self.reason[var(x)];
            let size = self.size(r);
            for k in 1..size {
                let q = self.arena[r as usize + HEADER + k];
                let v = var(q);
                if self.seen[v] || self.level[v] == 0 {
                    continue;
                }
                if self.reason[v] != NO_REASON && levels & (1 << (self.level[v] & 63)) != 0 {
                    self.seen[v] = true;
                    self.stack.push(q);
                    self.to_clear.push(v);
                } else {
                    for &u in &self.to_clear[top..] {
                        self.seen[u] = false;
                    }
                    self.to_clear.truncate(top);
                    return false;
                }
            }
        }
        true
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
            self.values[l as usize] = UNDEF;
            self.values[neg(l) as usize] = UNDEF;
            self.reason[v] = NO_REASON;
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
            let l = (v as Lit) << 1;
            if self.values[l as usize] == UNDEF {
                return Some(if self.phase[v] { l } else { l | 1 });
            }
        }
        None
    }

    fn locked(&self, c: u32) -> bool {
        let l = self.lits(c)[0];
        self.value(l) == TRUE && self.reason[var(l)] == c
    }

    /// Garde la moitié la plus utile des clauses apprises : les clauses « glue »
    /// (LBD ≤ 2) ne sont jamais jetées, les autres par LBD croissante.
    fn reduce_db(&mut self) {
        let mut learnts = std::mem::take(&mut self.learnts);
        learnts.sort_by_key(|&c| std::cmp::Reverse(self.arena[c as usize + 1]));
        let target = learnts.len() / 2;
        let mut removed = 0;
        learnts.retain(|&c| {
            if removed < target && self.arena[c as usize + 1] > 2 && !self.locked(c) {
                self.wasted += HEADER + self.size(c);
                self.arena[c as usize] |= DELETED;
                removed += 1;
                false
            } else {
                true
            }
        });
        self.stats.deleted += removed as u64;
        self.learnts = learnts;
        if self.wasted > self.arena.len() / 2 {
            self.collect_garbage();
        }
    }

    /// Recopie les clauses vivantes dans une arène neuve, et refait les listes
    /// de surveillance et les raisons avec les nouvelles références.
    fn collect_garbage(&mut self) {
        let mut fresh = Vec::with_capacity(self.arena.len() - self.wasted);
        let mut moved = vec![NO_REASON; 0];
        moved.resize(self.arena.len(), NO_REASON);
        let mut c = 0;
        while c < self.arena.len() {
            let head = self.arena[c];
            let size = (head & SIZE_MASK) as usize;
            if head & DELETED == 0 {
                moved[c] = fresh.len() as u32;
                fresh.extend_from_slice(&self.arena[c..c + HEADER + size]);
            }
            c += HEADER + size;
        }
        for r in self.reason.iter_mut() {
            if *r != NO_REASON {
                *r = moved[*r as usize];
            }
        }
        for c in self.learnts.iter_mut() {
            *c = moved[*c as usize];
        }
        self.arena = fresh;
        self.wasted = 0;
        for w in self.watches.iter_mut() {
            w.clear();
        }
        let mut c = 0;
        while c < self.arena.len() {
            let size = (self.arena[c] & SIZE_MASK) as usize;
            let (a, b) = (self.arena[c + HEADER], self.arena[c + HEADER + 1]);
            let binary = size == 2;
            self.watches[a as usize].push(Watch { cref: c as u32, blocker: b, binary });
            self.watches[b as usize].push(Watch { cref: c as u32, blocker: a, binary });
            c += HEADER + size;
        }
    }

    pub fn solve(&mut self) -> Outcome {
        if self.unsat || self.propagate().is_some() {
            return Outcome::Unsat;
        }
        let mut restart_idx = 0;
        let mut next_reduce = 2000u64;
        let mut learnt = Vec::new();
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
                    let back = self.analyze(confl, &mut learnt);
                    self.cancel_until(back);
                    if learnt.len() == 1 {
                        self.enqueue(learnt[0], NO_REASON);
                    } else {
                        let lbd = self.lbd(&learnt);
                        let cref = self.attach(&learnt, true, lbd);
                        self.enqueue(learnt[0], cref);
                    }
                    self.stats.learnt += 1;
                    self.var_inc /= 0.95;
                    if self.max_conflicts.is_some_and(|m| self.stats.conflicts >= m) {
                        return Outcome::Unknown;
                    }
                } else {
                    if conflicts_here >= budget {
                        self.stats.restarts += 1;
                        self.cancel_until(0);
                        break;
                    }
                    if self.stats.conflicts >= next_reduce {
                        next_reduce = self.stats.conflicts + 2000 + 300 * (self.stats.deleted / 1000);
                        self.reduce_db();
                    }
                    match self.pick_branch() {
                        None => {
                            let model = (0..self.nvars).map(|v| self.values[v << 1] == TRUE).collect();
                            return Outcome::Sat(model);
                        }
                        Some(l) => {
                            self.stats.decisions += 1;
                            self.trail_lim.push(self.trail.len());
                            self.enqueue(l, NO_REASON);
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
