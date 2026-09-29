use hotaru_kernel_bridge::{Error, Result, Term, Theory, Type, beta, check, conclusion, mp, refl};

#[test]
fn typed_rules_keep_their_object_kinds_and_context() -> Result<()> {
    let theory = Theory::new()?;
    let other = Theory::new()?;
    let boolean = Type::bool()?;
    let p = Term::free("p", &boolean)?;

    let theorem = refl(&theory, &p)?;
    assert_eq!(conclusion(&theorem), Term::equal(&p, &p)?);

    let implication = theory.disch(&p, &theory.assume(&p)?)?;
    assert_eq!(
        conclusion(&mp(&theory, &implication, &theory.assume(&p)?)?),
        p
    );

    let checked = check(&theory, &p)?;
    assert_eq!(checked.ty(), boolean);
    assert!(matches!(
        other.beta_checked(&checked),
        Err(Error::TheoryMismatch)
    ));

    let bound = Term::bound(0)?;
    let identity = Term::lambda(&boolean, &bound)?;
    let application = Term::app(&identity, &p)?;
    let checked_application = check(&theory, &application)?;
    let beta_theorem = beta(&theory, &checked_application)?;
    assert_eq!(conclusion(&beta_theorem), Term::equal(&application, &p)?);

    Ok(())
}
