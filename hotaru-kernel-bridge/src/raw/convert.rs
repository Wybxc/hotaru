//! Helpers for constructing and decoding Lean values used by the bridge.

use super::{
    error::{Result, checked},
    exports::{hotaru_lean_binding, hotaru_lean_checked_term_pair, hotaru_lean_equation_pair},
    runtime::{Handle, Obj},
};

pub(super) fn string(value: Handle) -> String {
    std::str::from_utf8(value.bytes())
        .expect("Lean returned invalid UTF-8")
        .to_owned()
}

pub(super) fn bindings(items: &[(&str, &Handle)]) -> Handle {
    items.iter().fold(Handle::array(), |array, (name, ty)| {
        let value = unsafe {
            Handle::from_raw(hotaru_lean_binding(
                Handle::string(name).into_raw(),
                ty.argument(),
            ))
        };
        array.push(value)
    })
}

pub(super) fn equation_pairs(state: Obj, items: &[(&Handle, &Handle)]) -> Handle {
    let state = unsafe { Handle::from_raw(state) };
    items
        .iter()
        .fold(Handle::array(), |array, (target, theorem)| {
            let pair = unsafe {
                Handle::from_raw(hotaru_lean_equation_pair(
                    state.argument(),
                    target.argument(),
                    theorem.argument(),
                ))
            };
            array.push(pair)
        })
}

pub(super) fn checked_term_pairs(state: Obj, items: &[(&Handle, &Handle)]) -> Handle {
    let state = unsafe { Handle::from_raw(state) };
    items
        .iter()
        .fold(Handle::array(), |array, (target, value)| {
            let pair = unsafe {
                Handle::from_raw(hotaru_lean_checked_term_pair(
                    state.argument(),
                    target.argument(),
                    value.argument(),
                ))
            };
            array.push(pair)
        })
}

pub(super) fn result_string(raw: Obj) -> Result<String> {
    Ok(string(unsafe { checked(raw)? }))
}
