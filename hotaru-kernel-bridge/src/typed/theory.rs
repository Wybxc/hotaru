//! Theory state and theorem/proof operations.
//!
//! Keeping this stateful layer separate from the typed syntax modules leaves a clear
//! boundary for future rewrite and proof-search APIs.

use crate::{
    Error, Result, raw as bridge, ready,
    typed::{
        context::Context,
        foundation::Foundation,
        syntax::{Name, Source, SourceKind},
        term::{CachedCheckedTerm, CheckedTerm, Term},
        theorem::Theorem,
        type_::Type,
    },
};
use std::rc::Rc;

#[derive(Clone)]
pub struct Theory {
    pub(super) context: Rc<Context>,
}

impl std::fmt::Debug for Theory {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Theory").finish_non_exhaustive()
    }
}

pub(super) fn sources(array: bridge::runtime::Handle) -> Result<Vec<Source>> {
    (0..bridge::sources_count(&array))
        .map(|index| {
            let source = bridge::sources_get(&array, index).map_err(Error::from)?;
            let kind = match bridge::source_kind(&source) {
                0 => SourceKind::TheoryFile,
                1 => SourceKind::Checkpoint,
                _ => unreachable!("Lean returned an invalid source kind"),
            };
            Ok(Source {
                kind,
                artifact: bridge::source_artifact(&source),
            })
        })
        .collect()
}

impl Theory {
    pub fn new() -> Result<Self> {
        ready()?;
        Ok(Self {
            context: Rc::new(Context {
                value: bridge::new_state(),
                parent: None,
                edge: None,
            }),
        })
    }

    /// Records an additional source in a new descendant theory.
    /// This does not load or authenticate a file.
    pub fn with_source(&self, source: &Source) -> Result<Theory> {
        let source = source.to_native()?;
        let edge = bridge::mark_theory(&self.context.value, &source).map_err(Error::from)?;
        Ok(self.extend(edge))
    }

    /// Distinct sources of this theory's construction, including definition premises.
    pub fn sources(&self) -> Result<Vec<Source>> {
        sources(bridge::theory_sources(&self.context.value))
    }

    fn owns(&self, theorem: &Theorem) -> Result<()> {
        if Rc::ptr_eq(&self.context, &theorem.context) {
            Ok(())
        } else {
            Err(Error::TheoryMismatch)
        }
    }

    fn owns_checked(&self, term: &CheckedTerm) -> Result<()> {
        if Rc::ptr_eq(&self.context, &term.context) {
            Ok(())
        } else {
            Err(Error::TheoryMismatch)
        }
    }

    pub(super) fn theorem(&self, value: bridge::runtime::Handle) -> Theorem {
        Theorem {
            value,
            context: self.context.clone(),
        }
    }

    pub fn check(&self, term: &Term) -> Result<Type> {
        Ok(Type {
            value: bridge::check(&self.context.value, &term.value).map_err(Error::from)?,
        })
    }

    /// Checks a term for repeated inference in this exact theory.
    /// The term retains one checked representation for this theory and returns a clone to callers.
    pub fn check_term(&self, term: &Term) -> Result<CheckedTerm> {
        if let Some(cached) = term.checked.borrow().as_ref()
            && Rc::ptr_eq(&self.context, &cached.context)
        {
            return Ok(cached.value.clone());
        }

        let checked = CheckedTerm {
            value: bridge::check_term(&self.context.value, &term.value).map_err(Error::from)?,
            context: self.context.clone(),
        };
        term.checked.borrow_mut().replace(CachedCheckedTerm {
            context: self.context.clone(),
            value: checked.clone(),
        });
        Ok(checked)
    }

    pub fn foundation(&self, which: Foundation) -> Result<Theorem> {
        Ok(self
            .theorem(bridge::foundation(&self.context.value, which as u64).map_err(Error::from)?))
    }

    pub fn assume(&self, term: &Term) -> Result<Theorem> {
        Ok(self.theorem(bridge::assume(&self.context.value, &term.value).map_err(Error::from)?))
    }

    pub fn assume_checked(&self, term: &CheckedTerm) -> Result<Theorem> {
        self.owns_checked(term)?;
        Ok(self.theorem(
            bridge::assume_checked(&self.context.value, &term.value).map_err(Error::from)?,
        ))
    }

    pub fn refl(&self, term: &Term) -> Result<Theorem> {
        Ok(self.theorem(bridge::refl(&self.context.value, &term.value).map_err(Error::from)?))
    }

    pub fn refl_checked(&self, term: &CheckedTerm) -> Result<Theorem> {
        self.owns_checked(term)?;
        Ok(self.theorem(bridge::refl_checked(&self.context.value, &term.value)))
    }

    pub fn beta(&self, term: &Term) -> Result<Theorem> {
        Ok(self.theorem(bridge::beta(&self.context.value, &term.value).map_err(Error::from)?))
    }

    pub fn beta_checked(&self, term: &CheckedTerm) -> Result<Theorem> {
        self.owns_checked(term)?;
        Ok(self
            .theorem(bridge::beta_checked(&self.context.value, &term.value).map_err(Error::from)?))
    }

    pub fn mk_comb(&self, a: &Theorem, b: &Theorem) -> Result<Theorem> {
        self.owns(a)?;
        self.owns(b)?;
        Ok(self.theorem(
            bridge::mk_comb(&self.context.value, &a.value, &b.value).map_err(Error::from)?,
        ))
    }

    pub fn mp(&self, a: &Theorem, b: &Theorem) -> Result<Theorem> {
        self.owns(a)?;
        self.owns(b)?;
        Ok(self.theorem(bridge::mp(&self.context.value, &a.value, &b.value).map_err(Error::from)?))
    }

    pub fn deduct_antisym(&self, a: &Theorem, b: &Theorem) -> Result<Theorem> {
        self.owns(a)?;
        self.owns(b)?;
        Ok(self.theorem(bridge::deduct_antisym(
            &self.context.value,
            &a.value,
            &b.value,
        )))
    }

    /// Applies structural contraction to the theorem's assumption context.
    pub fn contract(&self, theorem: &Theorem) -> Result<Theorem> {
        self.owns(theorem)?;
        Ok(self.theorem(bridge::contract(&self.context.value, &theorem.value)))
    }

    pub fn trans(&self, a: &Theorem, b: &Theorem) -> Result<Theorem> {
        self.owns(a)?;
        self.owns(b)?;
        Ok(self
            .theorem(bridge::trans(&self.context.value, &a.value, &b.value).map_err(Error::from)?))
    }

    pub fn eq_mp(&self, a: &Theorem, b: &Theorem) -> Result<Theorem> {
        self.owns(a)?;
        self.owns(b)?;
        Ok(self
            .theorem(bridge::eq_mp(&self.context.value, &a.value, &b.value).map_err(Error::from)?))
    }

    pub fn symm(&self, theorem: &Theorem) -> Result<Theorem> {
        self.owns(theorem)?;
        Ok(self.theorem(bridge::symm(&self.context.value, &theorem.value).map_err(Error::from)?))
    }

    pub fn abs(&self, name: &str, ty: &Type, theorem: &Theorem) -> Result<Theorem> {
        self.owns(theorem)?;
        Ok(self.theorem(
            bridge::abs(&self.context.value, name, &ty.value, &theorem.value)
                .map_err(Error::from)?,
        ))
    }

    pub fn disch(&self, term: &Term, theorem: &Theorem) -> Result<Theorem> {
        self.owns(theorem)?;
        Ok(self.theorem(
            bridge::disch(&self.context.value, &term.value, &theorem.value).map_err(Error::from)?,
        ))
    }

    pub fn disch_checked(&self, term: &CheckedTerm, theorem: &Theorem) -> Result<Theorem> {
        self.owns_checked(term)?;
        self.owns(theorem)?;
        Ok(self.theorem(
            bridge::disch_checked(&self.context.value, &term.value, &theorem.value)
                .map_err(Error::from)?,
        ))
    }

    pub fn inst(&self, replacements: &[(&Term, &Term)], theorem: &Theorem) -> Result<Theorem> {
        self.owns(theorem)?;
        let checked_terms = replacements
            .iter()
            .map(|(_, value)| self.check_term(value))
            .collect::<Result<Vec<_>>>()?;
        let checked_pairs = replacements
            .iter()
            .zip(checked_terms.iter())
            .map(|((target, _), value)| (&target.value, &value.value))
            .collect::<Vec<_>>();

        Ok(self.theorem(
            bridge::inst_checked(&self.context.value, &checked_pairs, &theorem.value)
                .map_err(Error::from)?,
        ))
    }

    pub fn inst_type(&self, replacements: &[(&str, &Type)], theorem: &Theorem) -> Result<Theorem> {
        self.owns(theorem)?;
        let replacements = replacements
            .iter()
            .map(|(name, ty)| (*name, &ty.value))
            .collect::<Vec<_>>();
        Ok(self.theorem(
            bridge::inst_type(&self.context.value, &replacements, &theorem.value)
                .map_err(Error::from)?,
        ))
    }

    /// Applies a HOL4-style combined type and term instantiation rule.
    /// Both substitutions are validated by the kernel in one FFI call.
    pub fn inst_ty_term(
        &self,
        type_replacements: &[(&str, &Type)],
        term_replacements: &[(&Term, &Term)],
        theorem: &Theorem,
    ) -> Result<Theorem> {
        self.owns(theorem)?;
        let checked_terms = term_replacements
            .iter()
            .map(|(_, value)| self.check_term(value))
            .collect::<Result<Vec<_>>>()?;
        let checked_pairs = term_replacements
            .iter()
            .zip(checked_terms.iter())
            .map(|((target, _), value)| (&target.value, &value.value))
            .collect::<Vec<_>>();
        let type_replacements = type_replacements
            .iter()
            .map(|(name, ty)| (*name, &ty.value))
            .collect::<Vec<_>>();

        Ok(self.theorem(
            bridge::inst_ty_term_checked(
                &self.context.value,
                &type_replacements,
                &checked_pairs,
                &theorem.value,
            )
            .map_err(Error::from)?,
        ))
    }

    pub fn subst(
        &self,
        equations: &[(&Term, &Theorem)],
        template: &Term,
        theorem: &Theorem,
    ) -> Result<Theorem> {
        self.owns(theorem)?;
        for (_, equation) in equations {
            self.owns(equation)?;
        }
        let equations = equations
            .iter()
            .map(|(term, equation)| (&term.value, &equation.value))
            .collect::<Vec<_>>();
        Ok(self.theorem(
            bridge::subst(
                &self.context.value,
                &equations,
                &template.value,
                &theorem.value,
            )
            .map_err(Error::from)?,
        ))
    }

    fn extend(&self, edge: bridge::runtime::Handle) -> Theory {
        let value = bridge::extension_state(&self.context.value, &edge);
        Theory {
            context: Rc::new(Context {
                value,
                edge: Some(edge),
                parent: Some(self.context.clone()),
            }),
        }
    }

    fn extend_produced(&self, edge: bridge::runtime::Handle) -> Result<(Theory, Theorem)> {
        let value = bridge::extension_theorem(&self.context.value, &edge).map_err(Error::from)?;
        let theory = self.extend(edge);
        let theorem = theory.theorem(value);
        Ok((theory, theorem))
    }

    pub fn declare_type(&self, name: &Name, arity: u64) -> Result<Theory> {
        Ok(self.extend(
            bridge::declare_type(&self.context.value, &name.scope, &name.name, arity)
                .map_err(Error::from)?,
        ))
    }

    pub fn declare_const(&self, name: &Name, ty: &Type) -> Result<Theory> {
        Ok(self.extend(
            bridge::declare_const(&self.context.value, &name.scope, &name.name, &ty.value)
                .map_err(Error::from)?,
        ))
    }

    pub fn define_const(&self, name: &Name, body: &Term) -> Result<(Theory, Theorem)> {
        self.extend_produced(
            bridge::define_const(&self.context.value, &name.scope, &name.name, &body.value)
                .map_err(Error::from)?,
        )
    }

    pub fn define_type(
        &self,
        name: &Name,
        parameters: &[&str],
        predicate: &Term,
        nonempty: &Theorem,
    ) -> Result<(Theory, Theorem)> {
        self.owns(nonempty)?;
        self.extend_produced(
            bridge::define_type(
                &self.context.value,
                &name.scope,
                &name.name,
                parameters,
                &predicate.value,
                &nonempty.value,
            )
            .map_err(Error::from)?,
        )
    }

    /// Adds an assumption to the theory. Soundness is conditional on models satisfying it.
    pub fn add_axiom(&self, proposition: &Term) -> Result<(Theory, Theorem)> {
        self.extend_produced(
            bridge::add_axiom(&self.context.value, &proposition.value).map_err(Error::from)?,
        )
    }
}
