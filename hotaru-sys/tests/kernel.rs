use hotaru_sys::{
    Error, Foundation, KernelError as K, Name, Result, Term, TermKind, Theory, Type, TypeKind,
};

fn rejects<T: std::fmt::Debug>(result: Result<T>, error: Error) {
    assert_eq!(result.unwrap_err(), error);
}

// The runtime intentionally belongs to one thread; keep native scenarios together.
#[test]
fn kernel_handles() -> Result<()> {
    let base = Theory::new()?;
    let other = Theory::new()?;

    let b = Type::bool()?;
    let a = Type::var("a")?;
    let bb = Type::function(&b, &b)?;
    let aa = Type::function(&a, &a)?;

    let p = Term::free("p", &b)?;
    let q = Term::free("q", &b)?;
    let xa = Term::free("x", &a)?;
    let xb = Term::free("x", &b)?;
    let v0 = Term::bound(0)?;
    let id = Term::lambda(&b, &v0)?;
    let app = Term::app(&id, &p)?;
    let eqpp = Term::equal(&p, &p)?;

    assert_eq!(base.check(&id)?, bb);

    let rp = base.refl(&p)?;
    let ap = base.assume(&p)?;
    assert_eq!(rp.conclusion(), eqpp);
    assert_eq!(ap.conclusion(), p);
    assert_eq!(base.beta(&app)?.conclusion(), Term::equal(&app, &p)?);
    assert_eq!(base.abs("p", &b, &rp)?.conclusion(), Term::equal(&id, &id)?);

    let ri = base.refl(&id)?;
    assert_eq!(
        base.mk_comb(&ri, &rp)?.conclusion(),
        Term::equal(&app, &app)?
    );

    let dis = base.disch(&p, &ap)?;
    assert_eq!(dis.conclusion(), Term::imp(&p, &p)?);
    assert_eq!(base.mp(&dis, &ap)?.conclusion(), p);

    let sym = base.symm(&rp)?;
    assert_eq!(sym.conclusion(), eqpp);
    assert_eq!(base.trans(&rp, &sym)?.conclusion(), eqpp);
    assert_eq!(base.eq_mp(&rp, &ap)?.conclusion(), p);
    assert_eq!(
        base.inst(&[(&p, &q)], &rp)?.conclusion(),
        Term::equal(&q, &q)?
    );
    assert_eq!(
        base.inst_type(&[("a", &b)], &base.refl(&xa)?)?.conclusion(),
        Term::equal(&xb, &xb)?
    );

    let before = base.abs("x", &a, &base.refl(&xb)?)?;
    let free_lambda = Term::lambda(&b, &xb)?;
    assert_eq!(
        base.inst_type(&[("a", &b)], &before)?.conclusion(),
        Term::equal(&free_lambda, &free_lambda)?
    );

    let outer = Term::lambda(&b, &Term::lambda(&b, &Term::bound(1)?)?)?;
    let nested = Term::app(&outer, &p)?;
    assert_eq!(
        base.beta(&nested)?.conclusion(),
        Term::equal(&nested, &Term::lambda(&b, &p)?)?
    );

    assert_eq!(base.subst(&[(&p, &rp)], &p, &ap)?.conclusion(), p);

    for f in [
        Foundation::Eta,
        Foundation::Selection,
        Foundation::Infinity,
        Foundation::BoolCases,
    ] {
        assert_eq!(base.foundation(f)?.assumption_count(), 0);
    }

    rejects(base.assume(&id), Error::Kernel(K::NotBoolean));
    rejects(base.refl(&v0), Error::Kernel(K::UnboundVariable));
    rejects(base.beta(&p), Error::Kernel(K::NotBetaRedex));
    rejects(base.mk_comb(&rp, &rp), Error::Kernel(K::NotFunction));
    rejects(base.mp(&rp, &ap), Error::Kernel(K::NotImplication));
    rejects(base.symm(&ap), Error::Kernel(K::NotEquation));
    rejects(
        base.abs("p", &b, &base.assume(&eqpp)?),
        Error::Kernel(K::FreeInAssumptions),
    );
    rejects(
        base.check(&Term::app(&p, &q)?),
        Error::Kernel(K::NotFunction),
    );
    rejects(
        base.check(&Term::app(&id, &id)?),
        Error::Kernel(K::TypeMismatch),
    );
    rejects(
        base.refl(&Term::constant(&Name::new("test", "missing"), &[])?),
        Error::Kernel(K::UnknownConstant),
    );
    rejects(base.inst(&[(&id, &p)], &rp), Error::Kernel(K::NotVariable));
    rejects(base.inst(&[(&p, &id)], &rp), Error::Kernel(K::TypeMismatch));
    rejects(
        base.trans(&rp, &base.refl(&q)?),
        Error::Kernel(K::TermMismatch),
    );
    rejects(
        base.eq_mp(&rp, &base.assume(&q)?),
        Error::Kernel(K::TermMismatch),
    );
    rejects(
        base.subst(&[(&p, &ap)], &p, &ap),
        Error::Kernel(K::NotEquation),
    );

    assert_eq!(bb.kind(), TypeKind::Function);
    assert_eq!(app.kind(), TermKind::Application);
    assert_eq!(bb.arity(), 2);
    assert_eq!(bb.child(0)?, b);
    assert_eq!(id.child(0)?, v0);
    assert_eq!(p.annotation()?, b);
    assert_eq!(v0.bound_index()?, 0);
    assert_eq!(Term::bound(u64::MAX)?.bound_index()?, u64::MAX);
    rejects(p.bound_index(), Error::WrongKind);
    rejects(id.child(1), Error::OutOfRange);
    rejects(app.annotation(), Error::WrongKind);

    assert_eq!(a.name()?, "a");
    assert_eq!(Term::free("a\0b\u{03b1}", &b)?.name()?, "a\0b\u{03b1}");

    assert_eq!(ap.assumptions()?, vec![p.clone()]);
    rejects(ap.assumption(1), Error::OutOfRange);
    assert_eq!(rp.assumption_count(), 0);

    let foreign = other.refl(&p)?;
    rejects(base.trans(&rp, &foreign), Error::TheoryMismatch);
    rejects(foreign.rebase(&base), Error::TheoryMismatch);

    let poly_name = Name::new("test", "poly");
    let poly = base.declare_const(&poly_name, &aa)?;
    let sibling = base.declare_const(&poly_name, &aa)?;
    let pc = Term::constant(&poly_name, &[("a", &b)])?;
    assert_eq!(poly.check(&pc)?, bb);
    rejects(base.check(&pc), Error::Kernel(K::UnknownConstant));
    rejects(poly.symm(&rp), Error::TheoryMismatch);

    let migrated = rp.rebase(&poly)?;
    assert_eq!(poly.symm(&migrated)?.conclusion(), eqpp);
    rejects(migrated.rebase(&sibling), Error::TheoryMismatch);
    rejects(migrated.rebase(&base), Error::TheoryMismatch);
    rejects(
        base.subst(&[(&p, &migrated)], &p, &ap),
        Error::TheoryMismatch,
    );

    assert_eq!(pc.scope()?, "test");
    assert_eq!(
        pc.constant_substitution()?,
        vec![("a".to_owned(), b.clone())]
    );
    rejects(p.constant_substitution(), Error::WrongKind);

    let box_name = Name::new("test", "box");
    let boxed = poly.declare_type(&box_name, 1)?;

    assert_eq!(rp.rebase(&boxed)?.conclusion(), eqpp);
    let box_type = Type::operator(&box_name, &[&b])?;
    assert_eq!(boxed.check(&Term::free("u", &box_type)?)?, box_type);

    let wrong = Type::operator(&box_name, &[])?;
    rejects(
        boxed.check(&Term::free("u", &wrong)?),
        Error::Kernel(K::InvalidType),
    );
    assert_eq!(box_type.scope()?, "test");
    rejects(
        boxed.declare_type(&box_name, 1),
        Error::Kernel(K::DuplicateType),
    );
    rejects(
        poly.declare_const(&poly_name, &aa),
        Error::Kernel(K::DuplicateConstant),
    );
    rejects(
        base.define_const(&Name::new("test", "bad"), &p),
        Error::Kernel(K::FreeVariablesInDefinition),
    );

    let (defined, definition) = base.define_const(&Name::new("test", "id"), &id)?;
    drop(defined);
    let recovered = definition.theory();
    let formula = definition.conclusion();
    drop(definition);
    assert_eq!(recovered.check(&formula.child(0)?)?, bb);

    let truth = Term::equal(&id, &id)?;
    let pred = Term::lambda(&b, &truth)?;
    let falsehood = Term::equal(&id, &pred)?;
    let empty = Term::lambda(&b, &falsehood)?;
    let pred_eq = Term::equal(&pred, &empty)?;
    let exists = Term::imp(&pred_eq, &falsehood)?;

    let applied = base.mk_comb(&base.assume(&pred_eq)?, &base.refl(&truth)?)?;
    let left = base.beta(&Term::app(&pred, &truth)?)?;
    let right = base.beta(&Term::app(&empty, &truth)?)?;
    let chain = base.trans(&base.trans(&base.symm(&left)?, &applied)?, &right)?;
    let nonempty = base.disch(&pred_eq, &base.eq_mp(&chain, &ri)?)?;
    assert_eq!(nonempty.conclusion(), exists);

    let inhabited_name = Name::new("test", "inhabited");
    rejects(
        poly.define_type(&inhabited_name, &[], &pred, &nonempty),
        Error::TheoryMismatch,
    );
    rejects(
        base.define_type(&inhabited_name, &["a", "a"], &pred, &nonempty),
        Error::Kernel(K::DuplicateTypeParameter),
    );
    rejects(
        base.define_type(&inhabited_name, &[], &pred, &base.assume(&exists)?),
        Error::Kernel(K::NonemptyProofHasAssumptions),
    );

    let (inhabited, type_definition) = base.define_type(&inhabited_name, &[], &pred, &nonempty)?;
    assert_eq!(type_definition.assumption_count(), 0);
    let inhabited_type = Type::operator(&inhabited_name, &[])?;
    assert_eq!(
        inhabited.check(&Term::free("v", &inhabited_type)?)?,
        inhabited_type
    );

    let (axioms, axiom) = base.add_axiom(&p)?;
    assert_eq!(axiom.conclusion(), p);
    assert_eq!(axiom.assumption_count(), 0);
    assert_eq!(axioms.check(&axiom.conclusion())?, b);

    assert!(
        std::thread::spawn(|| matches!(Type::bool(), Err(Error::WrongThread)))
            .join()
            .unwrap()
    );

    for _ in 0..100 {
        let copy = rp.rebase(&boxed)?;
        let value = copy.conclusion();
        drop(copy);
        assert_eq!(value, eqpp);
    }

    assert_eq!(rp.rebase(&base)?.conclusion(), eqpp);

    drop(base);
    drop(p);
    assert_eq!(rp.conclusion(), eqpp);

    Ok(())
}
