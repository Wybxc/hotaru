//! Typed term construction, inspection, and checked-term values.

use super::{context::Context, syntax::Name, type_::Type};
use crate::{Error, Result, raw as bridge, ready};
use std::{cell::RefCell, rc::Rc};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TermKind {
    Free,
    Bound,
    Constant,
    Application,
    Lambda,
    Equality,
    Implication,
}

#[derive(Clone)]
pub struct Term {
    pub(super) value: bridge::runtime::Handle,
    pub(super) checked: Rc<RefCell<Option<CachedCheckedTerm>>>,
}

/// A term validated for one exact theory. Retaining it also retains the typed Lean term.
#[derive(Clone)]
pub struct CheckedTerm {
    pub(super) value: bridge::runtime::Handle,
    pub(super) context: Rc<Context>,
}

#[derive(Clone)]
pub(super) struct CachedCheckedTerm {
    pub(super) context: Rc<Context>,
    pub(super) value: CheckedTerm,
}

impl std::fmt::Debug for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Term").finish_non_exhaustive()
    }
}

impl std::fmt::Debug for CheckedTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CheckedTerm").finish_non_exhaustive()
    }
}

impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        bridge::term_eq(&self.value, &other.value)
    }
}

impl Eq for Term {}

impl Term {
    pub(super) fn from_value(value: bridge::runtime::Handle) -> Self {
        Self {
            value,
            checked: Rc::new(RefCell::new(None)),
        }
    }

    pub fn free(name: &str, ty: &Type) -> Result<Self> {
        Ok(Self::from_value(bridge::term_free(name, &ty.value)))
    }

    pub fn bound(index: u64) -> Result<Self> {
        ready()?;
        Ok(Self::from_value(bridge::term_bound(index)))
    }

    pub fn constant(name: &Name, inst: &[(&str, &Type)]) -> Result<Self> {
        ready()?;
        let inst = inst
            .iter()
            .map(|(name, ty)| (*name, &ty.value))
            .collect::<Vec<_>>();
        Ok(Self::from_value(bridge::term_const(
            &name.scope,
            &name.name,
            &inst,
        )))
    }

    pub fn lambda(ty: &Type, body: &Term) -> Result<Self> {
        Ok(Self::from_value(bridge::term_lam(&ty.value, &body.value)))
    }

    /// Binds free occurrences of `name` with `ty` in `body`.
    pub fn abstract_term(name: &str, ty: &Type, body: &Term) -> Result<Self> {
        Ok(Self::from_value(bridge::term_abstract(
            name,
            &ty.value,
            &body.value,
        )))
    }

    pub fn kind(&self) -> TermKind {
        match bridge::term_kind(&self.value) {
            0 => TermKind::Free,
            1 => TermKind::Bound,
            2 => TermKind::Constant,
            3 => TermKind::Application,
            4 => TermKind::Lambda,
            5 => TermKind::Equality,
            6 => TermKind::Implication,
            _ => unreachable!(),
        }
    }

    pub fn child(&self, index: u64) -> Result<Term> {
        Ok(Self::from_value(
            bridge::term_child(&self.value, index).map_err(Error::from)?,
        ))
    }

    pub fn annotation(&self) -> Result<Type> {
        Ok(Type {
            value: bridge::term_annotation(&self.value).map_err(Error::from)?,
        })
    }

    pub fn bound_index(&self) -> Result<u64> {
        bridge::bound_index(&self.value).map_err(Error::from)
    }

    pub fn constant_substitution(&self) -> Result<Vec<(String, Type)>> {
        let count = bridge::inst_count(&self.value).map_err(Error::from)?;
        (0..count)
            .map(|index| {
                Ok((
                    bridge::inst_name(&self.value, index).map_err(Error::from)?,
                    Type {
                        value: bridge::inst_value(&self.value, index).map_err(Error::from)?,
                    },
                ))
            })
            .collect()
    }

    pub fn app(a: &Term, b: &Term) -> Result<Self> {
        Ok(Self::from_value(bridge::term_app(&a.value, &b.value)))
    }

    pub fn equal(a: &Term, b: &Term) -> Result<Self> {
        Ok(Self::from_value(bridge::term_equal(&a.value, &b.value)))
    }

    pub fn imp(a: &Term, b: &Term) -> Result<Self> {
        Ok(Self::from_value(bridge::term_imp(&a.value, &b.value)))
    }

    pub fn name(&self) -> Result<String> {
        bridge::term_name(&self.value).map_err(Error::from)
    }

    pub fn scope(&self) -> Result<String> {
        bridge::term_scope(&self.value).map_err(Error::from)
    }
}

impl CheckedTerm {
    /// Returns the type established by the Lean checker.
    pub fn ty(&self) -> Type {
        Type {
            value: bridge::checked_type(&self.context.value, &self.value),
        }
    }
}
