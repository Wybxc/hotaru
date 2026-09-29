use hotaru::{Result, Term, Theorem, Theory, Type};
use std::{env, hint::black_box, time::Instant};

const BATCH: usize = 256;
const MARKER: &str = "HOTARU_BENCH";

struct Case {
    kind: String,
    parameter: usize,
    iterations: usize,
}

fn cases() -> Vec<Case> {
    env::var("HOTARU_BENCH_SPEC")
        .expect("HOTARU_BENCH_SPEC is required")
        .split(';')
        .map(|row| {
            let fields: Vec<_> = row.split(':').collect();
            assert_eq!(fields.len(), 3, "invalid benchmark case: {row}");
            let iterations = fields[2].parse().expect("invalid iteration count");
            assert!(iterations > 0 && iterations % BATCH == 0);
            Case {
                kind: fields[0].to_owned(),
                parameter: fields[1].parse().expect("invalid case parameter"),
                iterations,
            }
        })
        .collect()
}

fn setting(name: &str) -> usize {
    let value: usize = env::var(name)
        .unwrap_or_else(|_| panic!("{name} is required"))
        .parse()
        .unwrap_or_else(|_| panic!("invalid {name}"));
    assert!(value > 0);
    value
}

fn build(f: &Term, p: &Term, depth: usize) -> Result<Term> {
    let mut term = p.clone();
    for _ in 0..depth {
        term = Term::app(f, &term)?;
    }
    Ok(term)
}

fn sample<F>(iterations: usize, retain: bool, make: &mut F) -> Result<(u128, Theorem)>
where
    F: FnMut() -> Result<Theorem>,
{
    if retain {
        let mut results = Vec::with_capacity(iterations);
        let start = Instant::now();
        for _ in 0..iterations {
            results.push(make()?);
        }
        black_box(&results);
        let elapsed_ns = start.elapsed().as_nanos();
        return Ok((elapsed_ns, results.pop().expect("nonempty benchmark")));
    }

    let mut last = None;
    let start = Instant::now();
    for _ in 0..iterations / BATCH {
        let mut block = Vec::with_capacity(BATCH);
        for _ in 0..BATCH {
            block.push(make()?);
        }
        black_box(&block);
        last = block.pop();
    }
    let elapsed_ns = start.elapsed().as_nanos();
    Ok((elapsed_ns, last.expect("nonempty benchmark")))
}

fn measure<F>(
    case: &Case,
    trials: usize,
    warmup: usize,
    expected: &Term,
    assumptions: u64,
    mut make: F,
) -> Result<()>
where
    F: FnMut() -> Result<Theorem>,
{
    let retain = case.kind == "refl_retain";
    let (_, warm) = sample(warmup, retain, &mut make)?;
    assert_eq!(warm.conclusion(), *expected);
    assert_eq!(warm.assumption_count(), assumptions);

    for trial in 0..trials {
        let (elapsed_ns, theorem) = sample(case.iterations, retain, &mut make)?;
        assert_eq!(theorem.conclusion(), *expected);
        assert_eq!(theorem.assumption_count(), assumptions);
        println!(
            "{MARKER}\t{}\t{}\t{trial}\t{}\t{elapsed_ns}",
            case.kind, case.parameter, case.iterations
        );
    }
    Ok(())
}

fn equality_chain(theory: &Theory, vars: &[Term], start: usize, end: usize) -> Result<Theorem> {
    if start == end {
        return theory.refl(&vars[start]);
    }
    let first = Term::equal(&vars[start], &vars[start + 1])?;
    let mut chain = theory.assume(&first)?;
    for i in start + 1..end {
        let step = theory.assume(&Term::equal(&vars[i], &vars[i + 1])?)?;
        chain = theory.trans(&chain, &step)?;
    }
    Ok(chain)
}

fn run_case(
    case: &Case,
    theory: &Theory,
    boolean: &Type,
    f: &Term,
    p: &Term,
    trials: usize,
    warmup: usize,
) -> Result<()> {
    match case.kind.as_str() {
        "refl_reuse" | "refl_retain" => {
            let term = build(f, p, case.parameter)?;
            let expected = Term::equal(&term, &term)?;
            measure(case, trials, warmup, &expected, 0, || theory.refl(&term))
        }
        "refl_checked" => {
            let term = build(f, p, case.parameter)?;
            let expected = Term::equal(&term, &term)?;
            let checked = theory.check_term(&term)?;
            measure(case, trials, warmup, &expected, 0, || {
                theory.refl_checked(&checked)
            })
        }
        "refl_build" => {
            let term = build(f, p, case.parameter)?;
            let expected = Term::equal(&term, &term)?;
            measure(case, trials, warmup, &expected, 0, || {
                let term = build(f, p, case.parameter)?;
                theory.refl(&term)
            })
        }
        "assume" => measure(case, trials, warmup, p, 1, || theory.assume(p)),
        "eq_mp" => {
            let equality = theory.refl(p)?;
            let premise = theory.assume(p)?;
            measure(case, trials, warmup, p, 1, || {
                theory.eq_mp(&equality, &premise)
            })
        }
        "trans_hyps" => {
            let count = case.parameter;
            let vars: Vec<_> = (0..=2 * count)
                .map(|i| Term::free(&format!("x{i}"), boolean))
                .collect::<Result<_>>()?;
            let left = equality_chain(theory, &vars, 0, count)?;
            let right = equality_chain(theory, &vars, count, 2 * count)?;
            let expected = Term::equal(&vars[0], &vars[2 * count])?;
            measure(
                case,
                trials,
                warmup,
                &expected,
                (2 * count).try_into().unwrap(),
                || theory.trans(&left, &right),
            )
        }
        "trace" => {
            let fp = Term::app(f, p)?;
            measure(case, trials, warmup, &fp, 1, || {
                let tf = theory.refl(f)?;
                let tp = theory.refl(p)?;
                let app = theory.mk_comb(&tf, &tp)?;
                let chain = theory.trans(&app, &app)?;
                let premise = theory.assume(&fp)?;
                theory.eq_mp(&chain, &premise)
            })
        }
        other => panic!("unknown benchmark case: {other}"),
    }
}

fn main() -> Result<()> {
    let theory = Theory::new()?;
    let boolean = Type::bool()?;
    let p = Term::free("p", &boolean)?;
    let f = Term::free("f", &Type::function(&boolean, &boolean)?)?;
    let trials = setting("HOTARU_BENCH_TRIALS");
    let warmup = setting("HOTARU_BENCH_WARMUP");
    assert_eq!(warmup % BATCH, 0);
    for case in cases() {
        run_case(&case, &theory, &boolean, &f, &p, trials, warmup)?;
    }
    Ok(())
}
