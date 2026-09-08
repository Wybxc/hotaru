use hotaru_sys::{Result, Term, Theory, Type};

fn main() -> Result<()> {
    let theory = Theory::new()?;
    let boolean = Type::bool()?;
    let p = Term::free("p", &boolean)?;
    let theorem = theory.refl(&p)?;
    assert_eq!(theorem.conclusion(), Term::equal(&p, &p)?);
    println!(
        "Proved p = p with {} assumptions",
        theorem.assumption_count()
    );
    Ok(())
}
