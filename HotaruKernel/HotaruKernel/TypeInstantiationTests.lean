import HotaruKernel.TypeInstantiation
import HotaruKernel.PropositionalTests

namespace HotaruKernel.TypeInstantiationTests

open Examples

def run (s : Signature) (i : TypeSubst) (r : RawTerm) :
    Except KernelError (HolType × RawTerm) :=
  (instantiateTermChecked s i r).map (fun c => (c.type, c.term.raw))

def alpha : HolType := .var "a"
def beta : HolType := .var "b"
def toBool : TypeSubst := [("a", .bool), ("b", .bool)]

example : run {} toBool (.fvar "x" alpha) = .ok (.bool, x) := by decide +kernel
example : run {} [] identity = .ok (.fn .bool .bool, identity) := by decide +kernel
example : run {} toBool (.lam alpha (.bvar 0)) =
    .ok (.fn .bool .bool, identity) := by decide +kernel
example : run {} toBool (.lam alpha (.lam beta (.bvar 1))) =
    .ok (.fn .bool (.fn .bool .bool), Tests.nested) := by decide +kernel

-- A free x remains free when its type merges with the surrounding binder's type.
example : run {} toBool (.lam alpha (.fvar "x" beta)) =
    .ok (.fn .bool .bool, .lam .bool x) := by decide +kernel

def merging : RawTerm :=
  .equal (.app (.fvar "f" (.fn alpha beta)) (.fvar "x" alpha)) (.fvar "x" beta)
example : run {} toBool merging =
    .ok (.bool, .equal (.app (.fvar "f" (.fn .bool .bool)) x) x) := by decide +kernel
example : run {} toBool (.imp (.equal (.fvar "x" alpha) (.fvar "y" alpha)) z) =
    .ok (.bool, .imp (.equal x y) z) := by decide +kernel

example : run {} [("a", beta), ("b", .bool)] (.fvar "x" alpha) =
    .ok (beta, .fvar "x" beta) := by decide +kernel
example : run {} [("a", .bool), ("a", beta)] (.fvar "x" alpha) =
    .ok (.bool, x) := by decide +kernel

example : run {} [("unused", .op Tests.boxName [])] x =
    .error .invalidType := by decide +kernel
example : run {} toBool (.bvar 0) = .error .unboundVariable := by decide +kernel
example : run {} toBool (.app (.fvar "x" alpha) (.fvar "x" beta)) =
    .error .notFunction := by decide +kernel

example : run Tests.signature [("a", .bool)] (.const Tests.constName []) =
    .ok (.fn .bool .bool, .const Tests.constName [("a", .bool)]) := by decide +kernel
example : run Tests.signature [("b", .bool)] (.const Tests.constName [("a", beta)]) =
    .ok (.fn .bool .bool, .const Tests.constName [("a", .bool), ("b", .bool)]) := by decide +kernel
example : run Tests.signature [("a", .op Tests.boxName [.bool])] (.fvar "v" alpha) =
    .ok (.op Tests.boxName [.bool], .fvar "v" (.op Tests.boxName [.bool])) := by decide +kernel
example : run Tests.signature [("a", .op Tests.boxName [])] (.fvar "v" alpha) =
    .error .invalidType := by decide +kernel

end HotaruKernel.TypeInstantiationTests
