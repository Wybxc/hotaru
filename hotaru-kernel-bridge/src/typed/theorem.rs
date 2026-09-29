//! Theorem inspection and provenance operations.

use crate::{
    Error, Result, raw as bridge,
    typed::{context::Context, syntax::Source, term::Term, theory::Theory},
};
use std::rc::Rc;

#[derive(Clone)]
pub struct Theorem {
    pub(super) value: bridge::runtime::Handle,
    pub(super) context: Rc<Context>,
}

impl std::fmt::Debug for Theorem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Theorem").finish_non_exhaustive()
    }
}

impl Theorem {
    /// Adds a claimed source while preserving all existing theorem and theory sources.
    pub fn with_source(&self, source: &Source) -> Result<Theorem> {
        let source = source.to_native()?;
        Ok(Theorem {
            value: bridge::mark_theorem(&self.context.value, &self.value, &source),
            context: self.context.clone(),
        })
    }

    /// Distinct sources inherited from the theory and all inference premises.
    pub fn sources(&self) -> Result<Vec<Source>> {
        crate::typed::theory::sources(bridge::theorem_sources(&self.context.value, &self.value))
    }

    pub fn theory(&self) -> Theory {
        Theory {
            context: self.context.clone(),
        }
    }

    pub fn conclusion(&self) -> Term {
        Term::from_value(bridge::conclusion(&self.context.value, &self.value))
    }

    pub fn assumption_count(&self) -> u64 {
        bridge::assumption_count(&self.context.value, &self.value)
    }

    pub fn assumption(&self, index: u64) -> Result<Term> {
        Ok(Term::from_value(
            bridge::assumption(&self.context.value, &self.value, index).map_err(Error::from)?,
        ))
    }

    pub fn assumptions(&self) -> Result<Vec<Term>> {
        (0..self.assumption_count())
            .map(|index| self.assumption(index))
            .collect()
    }

    pub fn rebase(&self, target: &Theory) -> Result<Theorem> {
        let mut cursor = &target.context;
        let mut path = Vec::new();

        while !Rc::ptr_eq(cursor, &self.context) {
            path.push(cursor.as_ref());
            cursor = cursor.parent.as_ref().ok_or(Error::TheoryMismatch)?;
        }

        let mut value = self.value.clone();
        for context in path.into_iter().rev() {
            value = bridge::rebase(
                &context.parent.as_ref().expect("path has a parent").value,
                context.edge.as_ref().expect("path has an extension edge"),
                &value,
            );
        }

        Ok(target.theorem(value))
    }
}
