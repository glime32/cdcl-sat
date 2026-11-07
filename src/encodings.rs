// Des problèmes traduits en CNF.
use crate::dimacs::Cnf;

fn at_most_one(clauses: &mut Vec<Vec<i32>>, vars: &[i32]) {
    for i in 0..vars.len() {
        for j in i + 1..vars.len() {
            clauses.push(vec![-vars[i], -vars[j]]);
        }
    }
}

fn exactly_one(clauses: &mut Vec<Vec<i32>>, vars: &[i32]) {
    clauses.push(vars.to_vec());
    at_most_one(clauses, vars);
}

// ---------------------------------------------------------------- sudoku

fn sv(r: usize, c: usize, d: usize) -> i32 {
    (81 * r + 9 * c + d + 1) as i32
}

/// grille : 81 caractères, chiffres 1-9, et '.' ou '0' pour les cases vides
pub fn sudoku(grid: &str) -> Result<Cnf, String> {
    let cells: Vec<char> = grid.chars().filter(|c| !c.is_whitespace() && *c != '|' && *c != '-' && *c != '+').collect();
    if cells.len() != 81 {
        return Err(format!("une grille fait 81 cases, j'en ai lu {}", cells.len()));
    }
    let mut cl = Vec::new();
    for a in 0..9 {
        for b in 0..9 {
            exactly_one(&mut cl, &(0..9).map(|d| sv(a, b, d)).collect::<Vec<_>>()); // case (a,b)
            exactly_one(&mut cl, &(0..9).map(|c| sv(a, c, b)).collect::<Vec<_>>()); // chiffre b dans la ligne a
            exactly_one(&mut cl, &(0..9).map(|r| sv(r, a, b)).collect::<Vec<_>>()); // chiffre b dans la colonne a
            let (br, bc) = (a / 3 * 3, a % 3 * 3);
            exactly_one(&mut cl, &(0..9).map(|k| sv(br + k / 3, bc + k % 3, b)).collect::<Vec<_>>()); // dans le bloc a
        }
    }
    for (i, ch) in cells.iter().enumerate() {
        match ch {
            '1'..='9' => cl.push(vec![sv(i / 9, i % 9, *ch as usize - '1' as usize)]),
            '.' | '0' | '_' => {}
            _ => return Err(format!("caractère inattendu « {ch} » dans la grille")),
        }
    }
    Ok(Cnf { nvars: 729, clauses: cl })
}

pub fn sudoku_grid(model: &[bool]) -> String {
    let mut s = String::new();
    for r in 0..9 {
        if r % 3 == 0 && r > 0 {
            s += "------+-------+------\n";
        }
        for c in 0..9 {
            if c % 3 == 0 && c > 0 {
                s += "| ";
            }
            let d = (0..9).find(|&d| model[sv(r, c, d) as usize - 1]).map(|d| d + 1).unwrap_or(0);
            s += &format!("{d} ");
        }
        s.pop();
        s.push('\n');
    }
    s
}

// ---------------------------------------------------------------- n reines

pub fn queens(n: usize) -> Cnf {
    let q = |r: usize, c: usize| (r * n + c + 1) as i32;
    let mut cl = Vec::new();
    for r in 0..n {
        exactly_one(&mut cl, &(0..n).map(|c| q(r, c)).collect::<Vec<_>>());
        at_most_one(&mut cl, &(0..n).map(|c| q(c, r)).collect::<Vec<_>>());
    }
    // diagonales : r - c constant, et r + c constant
    for d in 0..2 * n - 1 {
        let diag: Vec<i32> = (0..n).filter_map(|r| (d + r).checked_sub(n - 1).filter(|&c| c < n).map(|c| q(r, c))).collect();
        at_most_one(&mut cl, &diag);
        let anti: Vec<i32> = (0..n).filter_map(|r| d.checked_sub(r).filter(|&c| c < n).map(|c| q(r, c))).collect();
        at_most_one(&mut cl, &anti);
    }
    Cnf { nvars: n * n, clauses: cl }
}

pub fn queens_board(n: usize, model: &[bool]) -> String {
    let mut s = String::new();
    for r in 0..n {
        for c in 0..n {
            s += if model[r * n + c] { "♛ " } else if (r + c) % 2 == 0 { "· " } else { "  " };
        }
        s.push('\n');
    }
    s
}

// ------------------------------------------------------------ tiroirs

/// n+1 pigeons dans n trous : impossible, mais toute preuve par résolution
/// est de taille exponentielle (Haken, 1985). Le solveur souffre vite.
pub fn pigeons(n: usize) -> Cnf {
    let p = |i: usize, h: usize| (i * n + h + 1) as i32;
    let mut cl = Vec::new();
    for i in 0..=n {
        cl.push((0..n).map(|h| p(i, h)).collect());
    }
    for h in 0..n {
        at_most_one(&mut cl, &(0..=n).map(|i| p(i, h)).collect::<Vec<_>>());
    }
    Cnf { nvars: (n + 1) * n, clauses: cl }
}

// ------------------------------------------------------------ 3-SAT aléatoire

pub struct Rng(pub u64);

impl Rng {
    pub fn next(&mut self) -> u64 {
        // xorshift64*
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545F4914F6CDD1D)
    }
    pub fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

pub fn random_3sat(n: usize, m: usize, rng: &mut Rng) -> Cnf {
    let mut cl = Vec::with_capacity(m);
    for _ in 0..m {
        let mut c: Vec<i32> = Vec::with_capacity(3);
        while c.len() < 3 {
            let v = 1 + rng.below(n as u64) as i32;
            if c.iter().any(|x| x.abs() == v) {
                continue;
            }
            c.push(if rng.below(2) == 0 { v } else { -v });
        }
        cl.push(c);
    }
    Cnf { nvars: n, clauses: cl }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn queens_counts() {
        let c = queens(4);
        assert_eq!(c.nvars, 16);
        assert!(c.clauses.iter().all(|c| !c.is_empty()));
    }

    #[test]
    fn sudoku_rejects_bad_grid() {
        assert!(sudoku("123").is_err());
        assert!(sudoku(&"x".repeat(81)).is_err());
    }
}
