//! Errors returned by the typed bridge API.

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

impl KernelError {
    pub(super) fn from_native(code: u32) -> Self {
        match code {
            100 => Self::InvalidType,
            101 => Self::UnboundVariable,
            102 => Self::UnknownConstant,
            103 => Self::NotFunction,
            104 => Self::TypeMismatch,
            105 => Self::NotBoolean,
            106 => Self::NotEquation,
            107 => Self::NotBetaRedex,
            108 => Self::FreeInAssumptions,
            109 => Self::NotImplication,
            110 => Self::NotVariable,
            111 => Self::TermMismatch,
            112 => Self::InvalidSignature,
            113 => Self::DuplicateType,
            114 => Self::DuplicateConstant,
            115 => Self::FreeVariablesInDefinition,
            116 => Self::HiddenTypeVariables,
            117 => Self::DuplicateTypeParameter,
            118 => Self::MissingNonemptyProof,
            119 => Self::NonemptyProofHasAssumptions,
            120 => Self::NotPredicate,
            121 => Self::InvalidTheoremReference,
            _ => unreachable!("bridge returned an invalid kernel error code"),
        }
    }
}

#[allow(clippy::enum_variant_names)]
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

impl From<crate::raw::Error> for Error {
    fn from(error: crate::raw::Error) -> Self {
        match error {
            crate::raw::Error::WrongThread => Self::WrongThread,
            crate::raw::Error::Initialization => Self::Initialization,
            crate::raw::Error::WrongKind => Self::WrongKind,
            crate::raw::Error::OutOfRange => Self::OutOfRange,
            crate::raw::Error::Kernel(code) => Self::Kernel(KernelError::from_native(code)),
            crate::raw::Error::UnknownNativeError(code) => Self::UnknownNativeError(code),
        }
    }
}
