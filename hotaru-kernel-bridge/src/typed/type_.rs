//! Typed type syntax construction and inspection.

use super::syntax::Name;
use crate::{Error, Result, raw as bridge, ready};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeKind {
    Bool,
    Variable,
    Function,
    Operator,
}

#[derive(Clone)]
pub struct Type {
    pub(super) value: bridge::runtime::Handle,
}

impl std::fmt::Debug for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Type").finish_non_exhaustive()
    }
}

impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        bridge::type_eq(&self.value, &other.value)
    }
}

impl Eq for Type {}

impl Type {
    pub fn bool() -> Result<Self> {
        ready()?;
        Ok(Self {
            value: bridge::type_bool(),
        })
    }

    pub fn var(name: &str) -> Result<Self> {
        ready()?;
        Ok(Self {
            value: bridge::type_var(name),
        })
    }

    pub fn function(domain: &Type, range: &Type) -> Result<Self> {
        Ok(Self {
            value: bridge::type_fn(&domain.value, &range.value),
        })
    }

    pub fn operator(name: &Name, args: &[&Type]) -> Result<Self> {
        ready()?;
        let args = args.iter().map(|ty| &ty.value).collect::<Vec<_>>();
        Ok(Self {
            value: bridge::type_op(&name.scope, &name.name, &args),
        })
    }

    pub fn kind(&self) -> TypeKind {
        match bridge::type_kind(&self.value) {
            0 => TypeKind::Bool,
            1 => TypeKind::Variable,
            2 => TypeKind::Function,
            3 => TypeKind::Operator,
            _ => unreachable!(),
        }
    }

    pub fn arity(&self) -> u64 {
        bridge::type_arity(&self.value)
    }

    pub fn child(&self, index: u64) -> Result<Type> {
        Ok(Type {
            value: bridge::type_child(&self.value, index).map_err(Error::from)?,
        })
    }

    pub fn name(&self) -> Result<String> {
        bridge::type_name(&self.value).map_err(Error::from)
    }

    pub fn scope(&self) -> Result<String> {
        bridge::type_scope(&self.value).map_err(Error::from)
    }
}
