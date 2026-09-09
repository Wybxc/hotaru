import HotaruKernelFFI

namespace HotaruKernel.FFITests
open FFI

def state : Execution.State := Execution.initial
def p : RawTerm := termFree "p" (typeBool ())
def q : RawTerm := termFree "q" (typeBool ())
def identity : RawTerm := termLam (typeBool ()) (termBound 0)

def observe {s : Execution.State} (r : Result (Thm s.theory)) :
    Result (List RawTerm × RawTerm) :=
  r.map (fun th => (th.assumptions.map Term.raw, th.conclusion.raw))

def composed : Result (Thm state.theory) := do
  let a ← refl state identity
  let b ← refl state p
  let c ← mkComb state a b
  symm state c

example : observe composed = .ok ([], .equal (.app identity p) (.app identity p)) := by
  decide +kernel
example : observe (assume state p) = .ok ([p], p) := by decide +kernel
example : observe (beta state (.app identity p)) = .ok ([], .equal (.app identity p) p) := by
  decide +kernel
example : observe (assume state identity) = .error 105 := by decide +kernel
example : checkTerm state (.bvar 0) = .error 101 := by decide +kernel
example : checkTerm state (.app p q) = .error 103 := by decide +kernel
example : checkTerm state (.const ⟨"missing", "c"⟩ []) = .error 102 := by decide +kernel

def badAbs : Result (Thm state.theory) := do
  abs state "p" .bool (← assume state (.equal p p))
example : observe badAbs = .error 108 := by decide +kernel

def merged : Result (Thm state.theory) := do
  instType state #[("a", .bool)] (← refl state (.fvar "x" (.var "a")))
example : observe merged = .ok ([], .equal (.fvar "x" .bool) (.fvar "x" .bool)) := by
  decide +kernel

example : typeChild (.fn (.var "a") .bool) 1 = .ok .bool := by decide +kernel
example : termChild (.lam .bool (.bvar 0)) 0 = .ok (.bvar 0) := by decide +kernel
example : termAnnotation (.lam .bool (.bvar 0)) = .ok .bool := by decide +kernel
example : termName (.app p q) = .error 6 := by decide +kernel
example : instValue (.const ⟨"test", "c"⟩ [("a", .bool)]) 0 = .ok .bool := by
  decide +kernel

def extended : Result (Extension state) := declareType state "test" "new" 0
def migrated : Result RawTerm := do
  let e ← extended
  let th ← refl state p
  pure (rebase state e th).conclusion.raw
example : migrated = .ok (.equal p p) := by decide +kernel

example : (defineType state "test" "t" #[] identity none).map (fun _ => ()) =
    .error 118 := by decide +kernel

end HotaruKernel.FFITests
