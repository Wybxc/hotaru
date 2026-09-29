//! Raw, type-erased calls into the generated HotaruKernel ABI.

use super::{convert, error, exports, runtime};
use convert::{bindings, checked_term_pairs, equation_pairs, result_string, string};
use error::{Result, checked};
use exports::*;

fn owned(raw: runtime::Obj) -> runtime::Handle {
    // Every direct export below returns one owned Lean reference.
    unsafe { runtime::Handle::from_raw(raw) }
}

pub fn new_state() -> runtime::Handle {
    owned(unsafe { hotaru_lean_new(runtime::Owned::unit().into_raw()) })
}

pub fn type_bool() -> runtime::Handle {
    owned(unsafe { hotaru_lean_type_bool(runtime::Owned::unit().into_raw()) })
}

pub fn type_var(name: &str) -> runtime::Handle {
    owned(unsafe { hotaru_lean_type_var(runtime::Handle::string(name).into_raw()) })
}

pub fn type_fn(domain: &runtime::Handle, range: &runtime::Handle) -> runtime::Handle {
    owned(unsafe { hotaru_lean_type_fn(domain.argument(), range.argument()) })
}

pub fn type_op(scope: &str, name: &str, args: &[&runtime::Handle]) -> runtime::Handle {
    let args = args.iter().fold(runtime::Handle::array(), |array, arg| {
        array.push((*arg).clone())
    });
    owned(unsafe {
        hotaru_lean_type_op(
            runtime::Handle::string(scope).into_raw(),
            runtime::Handle::string(name).into_raw(),
            args.into_raw(),
        )
    })
}

pub fn type_eq(a: &runtime::Handle, b: &runtime::Handle) -> bool {
    unsafe { hotaru_lean_type_eq(a.argument(), b.argument()) != 0 }
}

pub fn type_kind(value: &runtime::Handle) -> u32 {
    unsafe { hotaru_lean_type_kind(value.argument()) }
}

pub fn type_arity(value: &runtime::Handle) -> u64 {
    unsafe { hotaru_lean_type_arity(value.argument()) }
}

pub fn type_child(value: &runtime::Handle, index: u64) -> Result<runtime::Handle> {
    unsafe { checked(hotaru_lean_type_child(value.argument(), index)) }
}

pub fn type_name(value: &runtime::Handle) -> Result<String> {
    unsafe { result_string(hotaru_lean_type_name(value.argument())) }
}

pub fn type_scope(value: &runtime::Handle) -> Result<String> {
    unsafe { result_string(hotaru_lean_type_scope(value.argument())) }
}

pub fn term_free(name: &str, ty: &runtime::Handle) -> runtime::Handle {
    owned(unsafe { hotaru_lean_term_free(runtime::Handle::string(name).into_raw(), ty.argument()) })
}

pub fn term_bound(index: u64) -> runtime::Handle {
    owned(unsafe { hotaru_lean_term_bound(index) })
}

pub fn term_const(scope: &str, name: &str, inst: &[(&str, &runtime::Handle)]) -> runtime::Handle {
    owned(unsafe {
        hotaru_lean_term_const(
            runtime::Handle::string(scope).into_raw(),
            runtime::Handle::string(name).into_raw(),
            bindings(inst).into_raw(),
        )
    })
}

pub fn term_app(function: &runtime::Handle, argument: &runtime::Handle) -> runtime::Handle {
    owned(unsafe { hotaru_lean_term_app(function.argument(), argument.argument()) })
}

pub fn term_lam(ty: &runtime::Handle, body: &runtime::Handle) -> runtime::Handle {
    owned(unsafe { hotaru_lean_term_lam(ty.argument(), body.argument()) })
}

pub fn term_abstract(name: &str, ty: &runtime::Handle, body: &runtime::Handle) -> runtime::Handle {
    owned(unsafe {
        hotaru_lean_term_abstract(
            runtime::Handle::string(name).into_raw(),
            ty.argument(),
            body.argument(),
        )
    })
}

pub fn term_equal(a: &runtime::Handle, b: &runtime::Handle) -> runtime::Handle {
    owned(unsafe { hotaru_lean_term_equal(a.argument(), b.argument()) })
}

pub fn term_imp(a: &runtime::Handle, b: &runtime::Handle) -> runtime::Handle {
    owned(unsafe { hotaru_lean_term_imp(a.argument(), b.argument()) })
}

pub fn term_eq(a: &runtime::Handle, b: &runtime::Handle) -> bool {
    unsafe { hotaru_lean_term_eq(a.argument(), b.argument()) != 0 }
}

pub fn term_kind(value: &runtime::Handle) -> u32 {
    unsafe { hotaru_lean_term_kind(value.argument()) }
}

pub fn term_child(value: &runtime::Handle, index: u64) -> Result<runtime::Handle> {
    unsafe { checked(hotaru_lean_term_child(value.argument(), index)) }
}

pub fn term_annotation(value: &runtime::Handle) -> Result<runtime::Handle> {
    unsafe { checked(hotaru_lean_term_annotation(value.argument())) }
}

pub fn bound_index(value: &runtime::Handle) -> Result<u64> {
    Ok(unsafe { checked(hotaru_lean_bound_index(value.argument()))? }.uint64())
}

pub fn inst_count(value: &runtime::Handle) -> Result<u64> {
    Ok(unsafe { checked(hotaru_lean_inst_count(value.argument()))? }.uint64())
}

pub fn inst_name(value: &runtime::Handle, index: u64) -> Result<String> {
    unsafe { result_string(hotaru_lean_inst_name(value.argument(), index)) }
}

pub fn inst_value(value: &runtime::Handle, index: u64) -> Result<runtime::Handle> {
    unsafe { checked(hotaru_lean_inst_value(value.argument(), index)) }
}

pub fn term_name(value: &runtime::Handle) -> Result<String> {
    unsafe { result_string(hotaru_lean_term_name(value.argument())) }
}

pub fn term_scope(value: &runtime::Handle) -> Result<String> {
    unsafe { result_string(hotaru_lean_term_scope(value.argument())) }
}

pub fn checked_type(state: &runtime::Handle, checked_term: &runtime::Handle) -> runtime::Handle {
    owned(unsafe { hotaru_lean_checked_type(state.argument(), checked_term.argument()) })
}

pub fn check(state: &runtime::Handle, term: &runtime::Handle) -> Result<runtime::Handle> {
    unsafe { checked(hotaru_lean_check(state.argument(), term.argument())) }
}

pub fn check_term(state: &runtime::Handle, term: &runtime::Handle) -> Result<runtime::Handle> {
    unsafe { checked(hotaru_lean_check_term(state.argument(), term.argument())) }
}

pub fn foundation(state: &runtime::Handle, index: u64) -> Result<runtime::Handle> {
    unsafe { checked(hotaru_lean_foundation(state.argument(), index)) }
}

pub fn assume(state: &runtime::Handle, term: &runtime::Handle) -> Result<runtime::Handle> {
    unsafe { checked(hotaru_lean_assume(state.argument(), term.argument())) }
}

pub fn assume_checked(state: &runtime::Handle, term: &runtime::Handle) -> Result<runtime::Handle> {
    unsafe {
        checked(hotaru_lean_assume_checked(
            state.argument(),
            term.argument(),
        ))
    }
}

pub fn refl(state: &runtime::Handle, term: &runtime::Handle) -> Result<runtime::Handle> {
    unsafe { checked(hotaru_lean_refl(state.argument(), term.argument())) }
}

pub fn refl_checked(state: &runtime::Handle, term: &runtime::Handle) -> runtime::Handle {
    owned(unsafe { hotaru_lean_refl_checked(state.argument(), term.argument()) })
}

pub fn beta(state: &runtime::Handle, term: &runtime::Handle) -> Result<runtime::Handle> {
    unsafe { checked(hotaru_lean_beta(state.argument(), term.argument())) }
}

pub fn beta_checked(state: &runtime::Handle, term: &runtime::Handle) -> Result<runtime::Handle> {
    unsafe { checked(hotaru_lean_beta_checked(state.argument(), term.argument())) }
}

pub fn abs(
    state: &runtime::Handle,
    name: &str,
    ty: &runtime::Handle,
    theorem: &runtime::Handle,
) -> Result<runtime::Handle> {
    unsafe {
        checked(hotaru_lean_abs(
            state.argument(),
            runtime::Handle::string(name).into_raw(),
            ty.argument(),
            theorem.argument(),
        ))
    }
}

pub fn mk_comb(
    state: &runtime::Handle,
    a: &runtime::Handle,
    b: &runtime::Handle,
) -> Result<runtime::Handle> {
    unsafe {
        checked(hotaru_lean_mk_comb(
            state.argument(),
            a.argument(),
            b.argument(),
        ))
    }
}

pub fn disch(
    state: &runtime::Handle,
    term: &runtime::Handle,
    theorem: &runtime::Handle,
) -> Result<runtime::Handle> {
    unsafe {
        checked(hotaru_lean_disch(
            state.argument(),
            term.argument(),
            theorem.argument(),
        ))
    }
}

pub fn disch_checked(
    state: &runtime::Handle,
    term: &runtime::Handle,
    theorem: &runtime::Handle,
) -> Result<runtime::Handle> {
    unsafe {
        checked(hotaru_lean_disch_checked(
            state.argument(),
            term.argument(),
            theorem.argument(),
        ))
    }
}

pub fn mp(
    state: &runtime::Handle,
    a: &runtime::Handle,
    b: &runtime::Handle,
) -> Result<runtime::Handle> {
    unsafe { checked(hotaru_lean_mp(state.argument(), a.argument(), b.argument())) }
}

pub fn deduct_antisym(
    state: &runtime::Handle,
    a: &runtime::Handle,
    b: &runtime::Handle,
) -> runtime::Handle {
    owned(unsafe { hotaru_lean_deduct_antisym(state.argument(), a.argument(), b.argument()) })
}

pub fn contract(state: &runtime::Handle, theorem: &runtime::Handle) -> runtime::Handle {
    owned(unsafe { hotaru_lean_contract(state.argument(), theorem.argument()) })
}

pub fn symm(state: &runtime::Handle, theorem: &runtime::Handle) -> Result<runtime::Handle> {
    unsafe { checked(hotaru_lean_symm(state.argument(), theorem.argument())) }
}

pub fn trans(
    state: &runtime::Handle,
    a: &runtime::Handle,
    b: &runtime::Handle,
) -> Result<runtime::Handle> {
    unsafe {
        checked(hotaru_lean_trans(
            state.argument(),
            a.argument(),
            b.argument(),
        ))
    }
}

pub fn eq_mp(
    state: &runtime::Handle,
    a: &runtime::Handle,
    b: &runtime::Handle,
) -> Result<runtime::Handle> {
    unsafe {
        checked(hotaru_lean_eq_mp(
            state.argument(),
            a.argument(),
            b.argument(),
        ))
    }
}

pub fn inst_checked(
    state: &runtime::Handle,
    replacements: &[(&runtime::Handle, &runtime::Handle)],
    theorem: &runtime::Handle,
) -> Result<runtime::Handle> {
    let pairs = checked_term_pairs(state.argument(), replacements);
    unsafe {
        checked(hotaru_lean_inst_checked(
            state.argument(),
            pairs.into_raw(),
            theorem.argument(),
        ))
    }
}

pub fn inst_type(
    state: &runtime::Handle,
    replacements: &[(&str, &runtime::Handle)],
    theorem: &runtime::Handle,
) -> Result<runtime::Handle> {
    unsafe {
        checked(hotaru_lean_inst_type(
            state.argument(),
            bindings(replacements).into_raw(),
            theorem.argument(),
        ))
    }
}

pub fn inst_ty_term_checked(
    state: &runtime::Handle,
    type_replacements: &[(&str, &runtime::Handle)],
    term_replacements: &[(&runtime::Handle, &runtime::Handle)],
    theorem: &runtime::Handle,
) -> Result<runtime::Handle> {
    let terms = checked_term_pairs(state.argument(), term_replacements);
    unsafe {
        checked(hotaru_lean_inst_ty_term_checked(
            state.argument(),
            bindings(type_replacements).into_raw(),
            terms.into_raw(),
            theorem.argument(),
        ))
    }
}

pub fn subst(
    state: &runtime::Handle,
    equations: &[(&runtime::Handle, &runtime::Handle)],
    template: &runtime::Handle,
    theorem: &runtime::Handle,
) -> Result<runtime::Handle> {
    let pairs = equation_pairs(state.argument(), equations);
    unsafe {
        checked(hotaru_lean_subst(
            state.argument(),
            pairs.into_raw(),
            template.argument(),
            theorem.argument(),
        ))
    }
}

pub fn extension_state(state: &runtime::Handle, extension: &runtime::Handle) -> runtime::Handle {
    owned(unsafe { hotaru_lean_extension_state(state.argument(), extension.argument()) })
}

pub fn extension_theorem(
    state: &runtime::Handle,
    extension: &runtime::Handle,
) -> Result<runtime::Handle> {
    unsafe {
        checked(hotaru_lean_extension_thm(
            state.argument(),
            extension.argument(),
        ))
    }
}

pub fn rebase(
    parent: &runtime::Handle,
    extension: &runtime::Handle,
    theorem: &runtime::Handle,
) -> runtime::Handle {
    owned(unsafe {
        hotaru_lean_rebase(parent.argument(), extension.argument(), theorem.argument())
    })
}

pub fn declare_type(
    state: &runtime::Handle,
    scope: &str,
    name: &str,
    arity: u64,
) -> Result<runtime::Handle> {
    unsafe {
        checked(hotaru_lean_declare_type(
            state.argument(),
            runtime::Handle::string(scope).into_raw(),
            runtime::Handle::string(name).into_raw(),
            arity,
        ))
    }
}

pub fn declare_const(
    state: &runtime::Handle,
    scope: &str,
    name: &str,
    ty: &runtime::Handle,
) -> Result<runtime::Handle> {
    unsafe {
        checked(hotaru_lean_declare_const(
            state.argument(),
            runtime::Handle::string(scope).into_raw(),
            runtime::Handle::string(name).into_raw(),
            ty.argument(),
        ))
    }
}

pub fn define_const(
    state: &runtime::Handle,
    scope: &str,
    name: &str,
    body: &runtime::Handle,
) -> Result<runtime::Handle> {
    unsafe {
        checked(hotaru_lean_define_const(
            state.argument(),
            runtime::Handle::string(scope).into_raw(),
            runtime::Handle::string(name).into_raw(),
            body.argument(),
        ))
    }
}

pub fn some_theorem(state: &runtime::Handle, theorem: &runtime::Handle) -> runtime::Handle {
    owned(unsafe { hotaru_lean_some_thm(state.argument(), theorem.argument()) })
}

pub fn define_type(
    state: &runtime::Handle,
    scope: &str,
    name: &str,
    parameters: &[&str],
    predicate: &runtime::Handle,
    proof: &runtime::Handle,
) -> Result<runtime::Handle> {
    let parameters = parameters
        .iter()
        .fold(runtime::Handle::array(), |array, parameter| {
            array.push(runtime::Handle::string(parameter))
        });
    let proof = some_theorem(state, proof);
    unsafe {
        checked(hotaru_lean_define_type(
            state.argument(),
            runtime::Handle::string(scope).into_raw(),
            runtime::Handle::string(name).into_raw(),
            parameters.into_raw(),
            predicate.argument(),
            proof.into_raw(),
        ))
    }
}

pub fn add_axiom(
    state: &runtime::Handle,
    proposition: &runtime::Handle,
) -> Result<runtime::Handle> {
    unsafe {
        checked(hotaru_lean_add_axiom(
            state.argument(),
            proposition.argument(),
        ))
    }
}

pub fn source(kind: u32, artifact: &str) -> Result<runtime::Handle> {
    unsafe {
        checked(hotaru_lean_source(
            kind,
            runtime::Handle::string(artifact).into_raw(),
        ))
    }
}

pub fn mark_theorem(
    state: &runtime::Handle,
    theorem: &runtime::Handle,
    source: &runtime::Handle,
) -> runtime::Handle {
    owned(unsafe {
        hotaru_lean_mark_theorem(state.argument(), theorem.argument(), source.argument())
    })
}

pub fn mark_theory(state: &runtime::Handle, source: &runtime::Handle) -> Result<runtime::Handle> {
    unsafe { checked(hotaru_lean_mark_theory(state.argument(), source.argument())) }
}

pub fn theorem_sources(state: &runtime::Handle, theorem: &runtime::Handle) -> runtime::Handle {
    owned(unsafe { hotaru_lean_theorem_sources(state.argument(), theorem.argument()) })
}

pub fn theory_sources(state: &runtime::Handle) -> runtime::Handle {
    owned(unsafe { hotaru_lean_theory_sources(state.argument()) })
}

pub fn sources_count(sources: &runtime::Handle) -> u64 {
    unsafe { hotaru_lean_sources_count(sources.argument()) }
}

pub fn sources_get(sources: &runtime::Handle, index: u64) -> Result<runtime::Handle> {
    unsafe { checked(hotaru_lean_sources_get(sources.argument(), index)) }
}

pub fn source_kind(source: &runtime::Handle) -> u32 {
    unsafe { hotaru_lean_source_kind(source.argument()) }
}

pub fn source_artifact(source: &runtime::Handle) -> String {
    string(owned(unsafe {
        hotaru_lean_source_artifact(source.argument())
    }))
}

pub fn conclusion(state: &runtime::Handle, theorem: &runtime::Handle) -> runtime::Handle {
    owned(unsafe { hotaru_lean_conclusion(state.argument(), theorem.argument()) })
}

pub fn assumption_count(state: &runtime::Handle, theorem: &runtime::Handle) -> u64 {
    unsafe { hotaru_lean_assumption_count(state.argument(), theorem.argument()) }
}

pub fn assumption(
    state: &runtime::Handle,
    theorem: &runtime::Handle,
    index: u64,
) -> Result<runtime::Handle> {
    unsafe {
        checked(hotaru_lean_assumption(
            state.argument(),
            theorem.argument(),
            index,
        ))
    }
}
