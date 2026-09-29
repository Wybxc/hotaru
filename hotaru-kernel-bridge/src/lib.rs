#![doc = "Typed safe Rust access to the verified Hotaru Lean kernel."]

//! The bridge's public API is entirely typed.  Raw Lean pointers, bindgen
//! declarations, and the type-erased handle live in the private `raw` module
//! and cannot be named by dependants.
//!
//! ```compile_fail
//! use hotaru_kernel_bridge::{Term, Theorem, Theory};
//!
//! let theory = Theory::new().unwrap();
//! let term = Term::bound(0).unwrap();
//! let theorem = theory.foundation(hotaru_kernel_bridge::Foundation::Eta).unwrap();
//! let _ = theory.mp(&term, &theorem);
//! ```
//!
//! ```compile_fail
//! use hotaru_kernel_bridge::{CheckedTerm, Term, Theory};
//!
//! fn only_checked(_: &CheckedTerm) {}
//! let term = Term::bound(0).unwrap();
//! only_checked(&term);
//! # let _ = Theory::new();
//! ```
//!
//! ```compile_fail
//! use hotaru_kernel_bridge::{check, Theorem, Term, Theory};
//!
//! let theory = Theory::new().unwrap();
//! let theorem: Theorem = panic!();
//! let _ = check(&theory, &theorem);
//! # let _ = Term::bound(0);
//! ```
//!
//! ```compile_fail
//! use hotaru_kernel_bridge::Handle;
//! ```
//!
//! ```compile_fail
//! use hotaru_kernel_bridge::{check, Theory, Type};
//!
//! let theory = Theory::new().unwrap();
//! let ty = Type::bool().unwrap();
//! let _ = check(&theory, &ty);
//! ```

mod raw;
mod typed;

fn ready() -> typed::Result<()> {
    raw::ensure_initialized().map_err(Into::into)
}

/// Ensures the Lean runtime is initialized on the current thread.
pub fn ensure_initialized() -> typed::Result<()> {
    ready()
}

pub use typed::{
    CheckedTerm, Error, Foundation, KernelError, Name, Result, Source, SourceKind, Term, TermKind,
    Theorem, Theory, Type, TypeKind,
};

/// Checks a raw term in one exact dynamic theory and returns the typed result.
pub fn check(theory: &Theory, term: &Term) -> Result<CheckedTerm> {
    theory.check_term(term)
}

/// Builds reflexivity in one exact dynamic theory.
pub fn refl(theory: &Theory, term: &Term) -> Result<Theorem> {
    theory.refl(term)
}

/// Builds beta reduction from a term already checked in `theory`.
pub fn beta(theory: &Theory, term: &CheckedTerm) -> Result<Theorem> {
    theory.beta_checked(term)
}

/// Applies modus ponens to two theorems from the same theory context.
pub fn mp(theory: &Theory, left: &Theorem, right: &Theorem) -> Result<Theorem> {
    theory.mp(left, right)
}

/// Returns the conclusion term of a theorem.
pub fn conclusion(theorem: &Theorem) -> Term {
    theorem.conclusion()
}
