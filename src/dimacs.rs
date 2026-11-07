// Lecture du format DIMACS CNF :
//   c commentaire
//   p cnf <variables> <clauses>
//   1 -3 4 0
pub struct Cnf {
    pub nvars: usize,
    pub clauses: Vec<Vec<i32>>,
}

pub fn parse(text: &str) -> Result<Cnf, String> {
    let mut nvars = None;
    let mut declared = 0;
    let mut clauses = Vec::new();
    let mut current = Vec::new();
    for (num, line) in text.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('c') || line.starts_with('%') {
            continue;
        }
        if line.starts_with('p') {
            let f: Vec<&str> = line.split_whitespace().collect();
            if f.len() != 4 || f[1] != "cnf" {
                return Err(format!("ligne {} : en-tête attendu « p cnf V C »", num + 1));
            }
            nvars = Some(f[2].parse::<usize>().map_err(|_| format!("ligne {} : nombre de variables illisible", num + 1))?);
            declared = f[3].parse::<usize>().unwrap_or(0);
            continue;
        }
        let n = nvars.ok_or_else(|| format!("ligne {} : clause avant l'en-tête p cnf", num + 1))?;
        for tok in line.split_whitespace() {
            let x: i32 = tok.parse().map_err(|_| format!("ligne {} : « {tok} » n'est pas un littéral", num + 1))?;
            if x == 0 {
                clauses.push(std::mem::take(&mut current));
            } else if x.unsigned_abs() as usize > n {
                return Err(format!("ligne {} : variable {} > {}", num + 1, x.abs(), n));
            } else {
                current.push(x);
            }
        }
    }
    if !current.is_empty() {
        clauses.push(current); // dernière clause sans 0 final : on tolère
    }
    let nvars = nvars.ok_or("pas d'en-tête p cnf")?;
    if declared != 0 && declared != clauses.len() {
        eprintln!("attention : {} clauses annoncées, {} lues", declared, clauses.len());
    }
    Ok(Cnf { nvars, clauses })
}

pub fn write(cnf: &Cnf) -> String {
    let mut s = format!("p cnf {} {}\n", cnf.nvars, cnf.clauses.len());
    for c in &cnf.clauses {
        for x in c {
            s += &x.to_string();
            s.push(' ');
        }
        s += "0\n";
    }
    s
}
