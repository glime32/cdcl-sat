mod dimacs;
mod encodings;
mod solver;

use dimacs::Cnf;
use encodings::Rng;
use solver::{Outcome, Solver, from_dimacs, to_dimacs};
use std::process::exit;
use std::time::Instant;

const AIDE: &str = "\
cdcl — un solveur SAT

  cdcl fichier.cnf              résout un fichier DIMACS (- pour l'entrée standard)
  cdcl sudoku GRILLE            81 caractères, '.' pour les cases vides
  cdcl reines N                 placer N reines qui ne se menacent pas
  cdcl pigeons N                N+1 pigeons dans N trous (impossible, et dur à prouver)
  cdcl aleatoire N RATIO [GRAINE]   3-SAT aléatoire, N variables, RATIO·N clauses
  cdcl transition [N] [ESSAIS]  la transition de phase du 3-SAT aléatoire
  cdcl genere sudoku|reines|pigeons|aleatoire ...   écrit le CNF au lieu de le résoudre

  --max-conflits N   abandonner après N conflits
";

fn fail(msg: &str) -> ! {
    eprintln!("cdcl : {msg}");
    exit(1)
}

fn arg<T: std::str::FromStr>(v: Option<&String>, nom: &str) -> T {
    v.and_then(|s| s.parse().ok()).unwrap_or_else(|| fail(&format!("il manque {nom} (voir cdcl --aide)")))
}

fn run(cnf: &Cnf, max: Option<u64>) -> (Outcome, Solver, f64) {
    let t = Instant::now();
    let mut s = Solver::new(cnf.nvars);
    s.max_conflicts = max;
    for c in &cnf.clauses {
        s.add_clause(&c.iter().map(|&x| from_dimacs(x)).collect::<Vec<_>>());
    }
    let r = s.solve();
    if let Outcome::Sat(m) = &r {
        // on ne fait pas confiance au solveur : on revérifie chaque clause
        if let Some(c) = cnf.clauses.iter().find(|c| !c.iter().any(|&x| m[(x.unsigned_abs() - 1) as usize] == (x > 0))) {
            fail(&format!("BUG : le modèle ne satisfait pas la clause {c:?}"));
        }
    }
    let dt = t.elapsed().as_secs_f64();
    (r, s, dt)
}

fn stats(s: &Solver, dt: f64) {
    let st = &s.stats;
    eprintln!(
        "c {:.3} s, {} conflits, {} décisions, {} propagations ({:.1} M/s), {} redémarrages, {} clauses apprises ({} oubliées)",
        dt, st.conflicts, st.decisions, st.propagations, st.propagations as f64 / dt.max(1e-9) / 1e6, st.restarts, st.learnt, st.deleted
    );
}

fn generate(kind: &str, rest: &[String]) -> Cnf {
    match kind {
        "sudoku" => encodings::sudoku(rest.first().unwrap_or_else(|| fail("il manque la grille"))).unwrap_or_else(|e| fail(&e)),
        "reines" => encodings::queens(arg(rest.first(), "N")),
        "pigeons" => encodings::pigeons(arg(rest.first(), "N")),
        "aleatoire" => {
            let n: usize = arg(rest.first(), "N");
            let ratio: f64 = arg(rest.get(1), "RATIO");
            let seed: u64 = rest.get(2).and_then(|s| s.parse().ok()).unwrap_or(1);
            encodings::random_3sat(n, (ratio * n as f64).round() as usize, &mut Rng(seed.max(1)))
        }
        _ => fail(&format!("je ne sais pas générer « {kind} »")),
    }
}

/// La proportion d'instances satisfiables chute brutalement autour de
/// 4,26 clauses par variable, et c'est là que les instances sont les plus dures.
fn transition(n: usize, trials: usize) {
    println!("3-SAT aléatoire, {n} variables, {trials} essais par ratio\n");
    println!(" ratio   SAT    conflits (médiane)");
    let mut rng = Rng(2026);
    let mut r = 3.0;
    while r <= 6.01 {
        let mut sat = 0;
        let mut conflicts = Vec::new();
        for _ in 0..trials {
            let cnf = encodings::random_3sat(n, (r * n as f64).round() as usize, &mut rng);
            let (out, s, _) = run(&cnf, None);
            if matches!(out, Outcome::Sat(_)) {
                sat += 1;
            }
            conflicts.push(s.stats.conflicts);
        }
        conflicts.sort();
        let med = conflicts[conflicts.len() / 2];
        let pct = 100 * sat / trials;
        let bar = "█".repeat(pct / 5);
        let hard = "▒".repeat(((med as f64 + 1.0).log2() * 1.5) as usize);
        println!(" {r:.2}   {pct:>3} % {bar:<20}  {med:>6} {hard}");
        r += 0.25;
    }
}

fn main() {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    let mut max = None;
    if let Some(i) = args.iter().position(|a| a == "--max-conflits") {
        max = Some(arg::<u64>(args.get(i + 1), "le nombre de conflits"));
        args.drain(i..=i + 1);
    }
    let Some(cmd) = args.first().cloned() else {
        print!("{AIDE}");
        exit(1)
    };
    let rest = &args[1..];
    match cmd.as_str() {
        "-h" | "--aide" | "--help" => print!("{AIDE}"),
        "transition" => transition(rest.first().and_then(|s| s.parse().ok()).unwrap_or(100), rest.get(1).and_then(|s| s.parse().ok()).unwrap_or(30)),
        "genere" => {
            let kind = rest.first().unwrap_or_else(|| fail("genere quoi ?"));
            print!("{}", dimacs::write(&generate(kind, &rest[1..])));
        }
        "sudoku" | "reines" | "pigeons" | "aleatoire" => {
            let cnf = generate(&cmd, rest);
            eprintln!("c {} variables, {} clauses", cnf.nvars, cnf.clauses.len());
            let (out, s, dt) = run(&cnf, max);
            match out {
                Outcome::Sat(m) => match cmd.as_str() {
                    "sudoku" => print!("{}", encodings::sudoku_grid(&m)),
                    "reines" => print!("{}", encodings::queens_board(arg(rest.first(), "N"), &m)),
                    _ => println!("satisfiable"),
                },
                Outcome::Unsat => println!("impossible (insatisfiable)"),
                Outcome::Unknown => println!("abandon : limite de conflits atteinte"),
            }
            stats(&s, dt);
        }
        path => {
            let text = if path == "-" {
                std::io::read_to_string(std::io::stdin()).unwrap_or_else(|e| fail(&e.to_string()))
            } else {
                std::fs::read_to_string(path).unwrap_or_else(|e| fail(&format!("{path} : {e}")))
            };
            let cnf = dimacs::parse(&text).unwrap_or_else(|e| fail(&e));
            eprintln!("c {} variables, {} clauses", cnf.nvars, cnf.clauses.len());
            let (out, s, dt) = run(&cnf, max);
            stats(&s, dt);
            match out {
                Outcome::Sat(m) => {
                    println!("s SATISFIABLE");
                    let lits: Vec<String> = (0..cnf.nvars)
                        .map(|v| to_dimacs(((v as u32) << 1) | if m[v] { 0 } else { 1 }).to_string())
                        .collect();
                    for chunk in lits.chunks(20) {
                        println!("v {}", chunk.join(" "));
                    }
                    println!("v 0");
                    exit(10);
                }
                Outcome::Unsat => {
                    println!("s UNSATISFIABLE");
                    exit(20);
                }
                Outcome::Unknown => println!("s UNKNOWN"),
            }
        }
    }
}
