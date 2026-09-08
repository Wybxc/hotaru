//! Safe Rust handles for the verified Lean kernel.
//! Handles are confined to the first thread that initializes the runtime.
//!
//! ```compile_fail
//! let ty = hotaru_sys::Type::bool().unwrap();
//! std::thread::spawn(move || drop(ty));
//! ```
//!
//! ```compile_fail
//! fn require_sync<T: Sync>() {}
//! require_sync::<hotaru_sys::Theorem>();
//! ```
mod raw;
mod runtime;

use raw::*;
use runtime::{Obj, Owned};
use std::{rc::Rc, sync::OnceLock, thread::ThreadId};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KernelError {
    InvalidType,
    UnboundVariable,
    UnknownConstant,
    NotFunction,
    TypeMismatch,
    NotBoolean,
    NotEquation,
    NotBetaRedex,
    FreeInAssumptions,
    NotImplication,
    NotVariable,
    TermMismatch,
    InvalidSignature,
    DuplicateType,
    DuplicateConstant,
    FreeVariablesInDefinition,
    HiddenTypeVariables,
    DuplicateTypeParameter,
    MissingNonemptyProof,
    NonemptyProofHasAssumptions,
    NotPredicate,
    InvalidTheoremReference,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    WrongThread,
    Initialization,
    WrongKind,
    TheoryMismatch,
    OutOfRange,
    Kernel(KernelError),
    UnknownNativeError(i32),
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::error::Error for Error {}
pub type Result<T> = std::result::Result<T, Error>;

fn ready() -> Result<()> {
    static INIT: OnceLock<(ThreadId, bool)> = OnceLock::new();
    let current = std::thread::current().id();
    let (owner, ok) = INIT.get_or_init(|| (current, runtime::initialize()));
    if *owner != current {
        Err(Error::WrongThread)
    } else if !ok {
        Err(Error::Initialization)
    } else {
        Ok(())
    }
}
fn error(code: i32) -> Error {
    match code {
        6 => Error::WrongKind,
        8 => Error::OutOfRange,
        100 => Error::Kernel(KernelError::InvalidType),
        101 => Error::Kernel(KernelError::UnboundVariable),
        102 => Error::Kernel(KernelError::UnknownConstant),
        103 => Error::Kernel(KernelError::NotFunction),
        104 => Error::Kernel(KernelError::TypeMismatch),
        105 => Error::Kernel(KernelError::NotBoolean),
        106 => Error::Kernel(KernelError::NotEquation),
        107 => Error::Kernel(KernelError::NotBetaRedex),
        108 => Error::Kernel(KernelError::FreeInAssumptions),
        109 => Error::Kernel(KernelError::NotImplication),
        110 => Error::Kernel(KernelError::NotVariable),
        111 => Error::Kernel(KernelError::TermMismatch),
        112 => Error::Kernel(KernelError::InvalidSignature),
        113 => Error::Kernel(KernelError::DuplicateType),
        114 => Error::Kernel(KernelError::DuplicateConstant),
        115 => Error::Kernel(KernelError::FreeVariablesInDefinition),
        116 => Error::Kernel(KernelError::HiddenTypeVariables),
        117 => Error::Kernel(KernelError::DuplicateTypeParameter),
        118 => Error::Kernel(KernelError::MissingNonemptyProof),
        119 => Error::Kernel(KernelError::NonemptyProofHasAssumptions),
        120 => Error::Kernel(KernelError::NotPredicate),
        121 => Error::Kernel(KernelError::InvalidTheoremReference),
        n => Error::UnknownNativeError(n),
    }
}
// Callers pass only owned results of the matching Lean exports.
unsafe fn checked(ptr: Obj) -> Result<Owned> {
    unsafe { Owned::from_raw(ptr) }.result().map_err(error)
}
fn string(value: Owned) -> String {
    std::str::from_utf8(value.bytes())
        .expect("Lean returned invalid UTF-8")
        .to_owned()
}
fn bindings(items: &[(&str, &Type)]) -> Owned {
    items.iter().fold(Owned::array(), |a, (n, t)| {
        a.push(unsafe {
            Owned::from_raw(hotaru_lean_binding(
                Owned::string(n).into_raw(),
                t.value.argument(),
            ))
        })
    })
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Name {
    pub scope: String,
    pub name: String,
}
impl Name {
    pub fn new(scope: impl Into<String>, name: impl Into<String>) -> Self {
        Self {
            scope: scope.into(),
            name: name.into(),
        }
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Foundation {
    Eta,
    Selection,
    Infinity,
    BoolCases,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeKind {
    Bool,
    Variable,
    Function,
    Operator,
}
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
pub struct Type {
    value: Owned,
}
#[derive(Clone)]
pub struct Term {
    value: Owned,
}
#[derive(Clone)]
pub struct Theory {
    context: Rc<Context>,
}
#[derive(Clone)]
pub struct Theorem {
    value: Owned,
    context: Rc<Context>,
}

struct Context {
    value: Owned,
    edge: Option<Owned>,
    parent: Option<Rc<Context>>,
}
impl Drop for Context {
    fn drop(&mut self) {
        let mut parent = self.parent.take();
        while let Some(rc) = parent {
            match Rc::try_unwrap(rc) {
                Ok(mut c) => parent = c.parent.take(),
                Err(_) => break,
            }
        }
    }
}
impl std::fmt::Debug for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Type").finish_non_exhaustive()
    }
}
impl std::fmt::Debug for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Term").finish_non_exhaustive()
    }
}
impl std::fmt::Debug for Theory {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Theory").finish_non_exhaustive()
    }
}
impl std::fmt::Debug for Theorem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Theorem").finish_non_exhaustive()
    }
}
impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        unsafe { hotaru_lean_type_eq(self.value.argument(), other.value.argument()) != 0 }
    }
}
impl Eq for Type {}
impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        unsafe { hotaru_lean_term_eq(self.value.argument(), other.value.argument()) != 0 }
    }
}
impl Eq for Term {}
impl Type {
    pub fn bool() -> Result<Self> {
        ready()?;
        Ok(Self {
            value: unsafe { Owned::from_raw(hotaru_lean_type_bool(Owned::unit().into_raw())) },
        })
    }
    pub fn var(name: &str) -> Result<Self> {
        ready()?;
        Ok(Self {
            value: unsafe { Owned::from_raw(hotaru_lean_type_var(Owned::string(name).into_raw())) },
        })
    }
    pub fn function(domain: &Type, range: &Type) -> Result<Self> {
        Ok(Self {
            value: unsafe {
                Owned::from_raw(hotaru_lean_type_fn(
                    domain.value.argument(),
                    range.value.argument(),
                ))
            },
        })
    }
    pub fn operator(name: &Name, args: &[&Type]) -> Result<Self> {
        ready()?;
        let args = args
            .iter()
            .fold(Owned::array(), |a, t| a.push(t.value.clone()));
        Ok(Self {
            value: unsafe {
                Owned::from_raw(hotaru_lean_type_op(
                    Owned::string(&name.scope).into_raw(),
                    Owned::string(&name.name).into_raw(),
                    args.into_raw(),
                ))
            },
        })
    }
    pub fn kind(&self) -> TypeKind {
        match unsafe { hotaru_lean_type_kind(self.value.argument()) } {
            0 => TypeKind::Bool,
            1 => TypeKind::Variable,
            2 => TypeKind::Function,
            3 => TypeKind::Operator,
            _ => unreachable!(),
        }
    }
    pub fn arity(&self) -> u64 {
        unsafe { hotaru_lean_type_arity(self.value.argument()) }
    }
    pub fn child(&self, index: u64) -> Result<Type> {
        Ok(Type {
            value: unsafe { checked(hotaru_lean_type_child(self.value.argument(), index))? },
        })
    }
}
impl Term {
    pub fn free(name: &str, ty: &Type) -> Result<Self> {
        Ok(Self {
            value: unsafe {
                Owned::from_raw(hotaru_lean_term_free(
                    Owned::string(name).into_raw(),
                    ty.value.argument(),
                ))
            },
        })
    }
    pub fn bound(index: u64) -> Result<Self> {
        ready()?;
        Ok(Self {
            value: unsafe { Owned::from_raw(hotaru_lean_term_bound(index)) },
        })
    }
    pub fn constant(name: &Name, inst: &[(&str, &Type)]) -> Result<Self> {
        ready()?;
        Ok(Self {
            value: unsafe {
                Owned::from_raw(hotaru_lean_term_const(
                    Owned::string(&name.scope).into_raw(),
                    Owned::string(&name.name).into_raw(),
                    bindings(inst).into_raw(),
                ))
            },
        })
    }
    pub fn lambda(ty: &Type, body: &Term) -> Result<Self> {
        Ok(Self {
            value: unsafe {
                Owned::from_raw(hotaru_lean_term_lam(
                    ty.value.argument(),
                    body.value.argument(),
                ))
            },
        })
    }
    pub fn kind(&self) -> TermKind {
        match unsafe { hotaru_lean_term_kind(self.value.argument()) } {
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
        Ok(Term {
            value: unsafe { checked(hotaru_lean_term_child(self.value.argument(), index))? },
        })
    }
    pub fn annotation(&self) -> Result<Type> {
        Ok(Type {
            value: unsafe { checked(hotaru_lean_term_annotation(self.value.argument()))? },
        })
    }
    pub fn bound_index(&self) -> Result<u64> {
        Ok(unsafe { checked(hotaru_lean_bound_index(self.value.argument()))? }.uint64())
    }
    pub fn constant_substitution(&self) -> Result<Vec<(String, Type)>> {
        let count = unsafe { checked(hotaru_lean_inst_count(self.value.argument()))? }.uint64();
        (0..count)
            .map(|i| {
                Ok((
                    string(unsafe { checked(hotaru_lean_inst_name(self.value.argument(), i))? }),
                    Type {
                        value: unsafe {
                            checked(hotaru_lean_inst_value(self.value.argument(), i))?
                        },
                    },
                ))
            })
            .collect()
    }
    pub fn app(a: &Term, b: &Term) -> Result<Self> {
        Ok(Self {
            value: unsafe {
                Owned::from_raw(hotaru_lean_term_app(a.value.argument(), b.value.argument()))
            },
        })
    }
    pub fn equal(a: &Term, b: &Term) -> Result<Self> {
        Ok(Self {
            value: unsafe {
                Owned::from_raw(hotaru_lean_term_equal(
                    a.value.argument(),
                    b.value.argument(),
                ))
            },
        })
    }
    pub fn imp(a: &Term, b: &Term) -> Result<Self> {
        Ok(Self {
            value: unsafe {
                Owned::from_raw(hotaru_lean_term_imp(a.value.argument(), b.value.argument()))
            },
        })
    }
}
impl Type {
    pub fn name(&self) -> Result<String> {
        Ok(string(unsafe {
            checked(hotaru_lean_type_name(self.value.argument()))?
        }))
    }
    pub fn scope(&self) -> Result<String> {
        Ok(string(unsafe {
            checked(hotaru_lean_type_scope(self.value.argument()))?
        }))
    }
}
impl Term {
    pub fn name(&self) -> Result<String> {
        Ok(string(unsafe {
            checked(hotaru_lean_term_name(self.value.argument()))?
        }))
    }
    pub fn scope(&self) -> Result<String> {
        Ok(string(unsafe {
            checked(hotaru_lean_term_scope(self.value.argument()))?
        }))
    }
}
impl Theory {
    pub fn new() -> Result<Self> {
        ready()?;
        Ok(Self {
            context: Rc::new(Context {
                value: unsafe { Owned::from_raw(hotaru_lean_new(Owned::unit().into_raw())) },
                parent: None,
                edge: None,
            }),
        })
    }
    fn arg(&self) -> Obj {
        self.context.value.argument()
    }
    fn owns(&self, th: &Theorem) -> Result<()> {
        if Rc::ptr_eq(&self.context, &th.context) {
            Ok(())
        } else {
            Err(Error::TheoryMismatch)
        }
    }
    fn theorem(&self, value: Owned) -> Theorem {
        Theorem {
            value,
            context: self.context.clone(),
        }
    }
    pub fn check(&self, term: &Term) -> Result<Type> {
        Ok(Type {
            value: unsafe { checked(hotaru_lean_check(self.arg(), term.value.argument()))? },
        })
    }
    pub fn foundation(&self, which: Foundation) -> Result<Theorem> {
        Ok(self.theorem(unsafe { checked(hotaru_lean_foundation(self.arg(), which as u64))? }))
    }
    pub fn assume(&self, term: &Term) -> Result<Theorem> {
        Ok(
            self.theorem(unsafe {
                checked(hotaru_lean_assume(self.arg(), term.value.argument()))?
            }),
        )
    }
    pub fn refl(&self, term: &Term) -> Result<Theorem> {
        Ok(self.theorem(unsafe { checked(hotaru_lean_refl(self.arg(), term.value.argument()))? }))
    }
    pub fn beta(&self, term: &Term) -> Result<Theorem> {
        Ok(self.theorem(unsafe { checked(hotaru_lean_beta(self.arg(), term.value.argument()))? }))
    }
    pub fn mk_comb(&self, a: &Theorem, b: &Theorem) -> Result<Theorem> {
        self.owns(a)?;
        self.owns(b)?;
        Ok(self.theorem(unsafe {
            checked(hotaru_lean_mk_comb(
                self.arg(),
                a.value.argument(),
                b.value.argument(),
            ))?
        }))
    }
    pub fn mp(&self, a: &Theorem, b: &Theorem) -> Result<Theorem> {
        self.owns(a)?;
        self.owns(b)?;
        Ok(self.theorem(unsafe {
            checked(hotaru_lean_mp(
                self.arg(),
                a.value.argument(),
                b.value.argument(),
            ))?
        }))
    }
    pub fn trans(&self, a: &Theorem, b: &Theorem) -> Result<Theorem> {
        self.owns(a)?;
        self.owns(b)?;
        Ok(self.theorem(unsafe {
            checked(hotaru_lean_trans(
                self.arg(),
                a.value.argument(),
                b.value.argument(),
            ))?
        }))
    }
    pub fn eq_mp(&self, a: &Theorem, b: &Theorem) -> Result<Theorem> {
        self.owns(a)?;
        self.owns(b)?;
        Ok(self.theorem(unsafe {
            checked(hotaru_lean_eq_mp(
                self.arg(),
                a.value.argument(),
                b.value.argument(),
            ))?
        }))
    }
    pub fn symm(&self, th: &Theorem) -> Result<Theorem> {
        self.owns(th)?;
        Ok(self.theorem(unsafe { checked(hotaru_lean_symm(self.arg(), th.value.argument()))? }))
    }
    pub fn abs(&self, name: &str, ty: &Type, th: &Theorem) -> Result<Theorem> {
        self.owns(th)?;
        Ok(self.theorem(unsafe {
            checked(hotaru_lean_abs(
                self.arg(),
                Owned::string(name).into_raw(),
                ty.value.argument(),
                th.value.argument(),
            ))?
        }))
    }
    pub fn disch(&self, term: &Term, th: &Theorem) -> Result<Theorem> {
        self.owns(th)?;
        Ok(self.theorem(unsafe {
            checked(hotaru_lean_disch(
                self.arg(),
                term.value.argument(),
                th.value.argument(),
            ))?
        }))
    }
    pub fn inst(&self, replacements: &[(&Term, &Term)], th: &Theorem) -> Result<Theorem> {
        self.owns(th)?;
        let pairs = replacements.iter().fold(Owned::array(), |a, (x, y)| {
            a.push(unsafe {
                Owned::from_raw(hotaru_lean_term_pair(
                    x.value.argument(),
                    y.value.argument(),
                ))
            })
        });
        Ok(self.theorem(unsafe {
            checked(hotaru_lean_inst(
                self.arg(),
                pairs.into_raw(),
                th.value.argument(),
            ))?
        }))
    }
    pub fn inst_type(&self, replacements: &[(&str, &Type)], th: &Theorem) -> Result<Theorem> {
        self.owns(th)?;
        Ok(self.theorem(unsafe {
            checked(hotaru_lean_inst_type(
                self.arg(),
                bindings(replacements).into_raw(),
                th.value.argument(),
            ))?
        }))
    }
    pub fn subst(
        &self,
        equations: &[(&Term, &Theorem)],
        template: &Term,
        th: &Theorem,
    ) -> Result<Theorem> {
        self.owns(th)?;
        for (_, equation) in equations {
            self.owns(equation)?;
        }
        let pairs = equations.iter().fold(Owned::array(), |a, (x, eq)| {
            a.push(unsafe {
                Owned::from_raw(hotaru_lean_equation_pair(
                    self.arg(),
                    x.value.argument(),
                    eq.value.argument(),
                ))
            })
        });
        Ok(self.theorem(unsafe {
            checked(hotaru_lean_subst(
                self.arg(),
                pairs.into_raw(),
                template.value.argument(),
                th.value.argument(),
            ))?
        }))
    }
    fn extend(&self, edge: Owned) -> Theory {
        let value =
            unsafe { Owned::from_raw(hotaru_lean_extension_state(self.arg(), edge.argument())) };
        Theory {
            context: Rc::new(Context {
                value,
                edge: Some(edge),
                parent: Some(self.context.clone()),
            }),
        }
    }
    fn extend_produced(&self, edge: Owned) -> Result<(Theory, Theorem)> {
        let value = unsafe { checked(hotaru_lean_extension_thm(self.arg(), edge.argument()))? };
        let theory = self.extend(edge);
        let th = theory.theorem(value);
        Ok((theory, th))
    }
    pub fn declare_type(&self, name: &Name, arity: u64) -> Result<Theory> {
        Ok(self.extend(unsafe {
            checked(hotaru_lean_declare_type(
                self.arg(),
                Owned::string(&name.scope).into_raw(),
                Owned::string(&name.name).into_raw(),
                arity,
            ))?
        }))
    }
    pub fn declare_const(&self, name: &Name, ty: &Type) -> Result<Theory> {
        Ok(self.extend(unsafe {
            checked(hotaru_lean_declare_const(
                self.arg(),
                Owned::string(&name.scope).into_raw(),
                Owned::string(&name.name).into_raw(),
                ty.value.argument(),
            ))?
        }))
    }
    pub fn define_const(&self, name: &Name, body: &Term) -> Result<(Theory, Theorem)> {
        self.extend_produced(unsafe {
            checked(hotaru_lean_define_const(
                self.arg(),
                Owned::string(&name.scope).into_raw(),
                Owned::string(&name.name).into_raw(),
                body.value.argument(),
            ))?
        })
    }
    pub fn define_type(
        &self,
        name: &Name,
        parameters: &[&str],
        predicate: &Term,
        nonempty: &Theorem,
    ) -> Result<(Theory, Theorem)> {
        self.owns(nonempty)?;
        let params = parameters
            .iter()
            .fold(Owned::array(), |a, p| a.push(Owned::string(p)));
        let proof =
            unsafe { Owned::from_raw(hotaru_lean_some_thm(self.arg(), nonempty.value.argument())) };
        self.extend_produced(unsafe {
            checked(hotaru_lean_define_type(
                self.arg(),
                Owned::string(&name.scope).into_raw(),
                Owned::string(&name.name).into_raw(),
                params.into_raw(),
                predicate.value.argument(),
                proof.into_raw(),
            ))?
        })
    }
    /// Adds an assumption to the theory. Soundness is conditional on models satisfying it.
    pub fn add_axiom(&self, proposition: &Term) -> Result<(Theory, Theorem)> {
        self.extend_produced(unsafe {
            checked(hotaru_lean_add_axiom(
                self.arg(),
                proposition.value.argument(),
            ))?
        })
    }
}
impl Theorem {
    pub fn theory(&self) -> Theory {
        Theory {
            context: self.context.clone(),
        }
    }
    pub fn conclusion(&self) -> Term {
        Term {
            value: unsafe {
                Owned::from_raw(hotaru_lean_conclusion(
                    self.context.value.argument(),
                    self.value.argument(),
                ))
            },
        }
    }
    pub fn assumption_count(&self) -> u64 {
        unsafe {
            hotaru_lean_assumption_count(self.context.value.argument(), self.value.argument())
        }
    }
    pub fn assumption(&self, index: u64) -> Result<Term> {
        Ok(Term {
            value: unsafe {
                checked(hotaru_lean_assumption(
                    self.context.value.argument(),
                    self.value.argument(),
                    index,
                ))?
            },
        })
    }
    pub fn assumptions(&self) -> Result<Vec<Term>> {
        (0..self.assumption_count())
            .map(|i| self.assumption(i))
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
            value = unsafe {
                Owned::from_raw(hotaru_lean_rebase(
                    context.parent.as_ref().unwrap().value.argument(),
                    context.edge.as_ref().unwrap().argument(),
                    value.into_raw(),
                ))
            };
        }
        Ok(target.theorem(value))
    }
}
