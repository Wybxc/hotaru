import HotaruKernel.Execution
import HotaruKernelTests.Foundation

namespace HotaruKernel.ExecutionTests

open Execution

def identity : RawTerm := .lam .bool (.bvar 0)
def trueRaw : RawTerm := .equal identity identity
def falseRaw : RawTerm := .equal identity (.lam .bool trueRaw)
def predicate : RawTerm := .lam .bool trueRaw
def emptyPredicate : RawTerm := .lam .bool falseRaw
def assumedEquation : RawTerm := .equal predicate emptyPredicate
def identityName : QName := ⟨"trace", "id"⟩
def typeName : QName := ⟨"trace", "subset"⟩
def selectedIdentity : RawTerm := .app (.const identityName [("a", .bool)]) trueRaw

-- Indices remain stable when declarations migrate the existing theorem table.
def completeTrace : List Command := [
  .declareType ⟨"trace", "token"⟩ 0,
  .declareConstant ⟨"trace", "seed"⟩ .bool,
  .defineConstant identityName (.lam (.var "a") (.bvar 0)),
  .infer (.instType [("a", .bool)] 4),
  .infer (.refl trueRaw),
  .infer (.mkComb 5 6),
  .infer (.beta (.app identity trueRaw)),
  .infer (.trans 7 8),
  .infer (.inst [] 9),
  .infer (.symm 10),
  .infer (.subst [] (.equal trueRaw selectedIdentity) 11),
  .infer (.abs "unused" .bool 12),
  .infer (.assume assumedEquation),
  .infer (.refl trueRaw),
  .infer (.mkComb 14 15),
  .infer (.beta (.app predicate trueRaw)),
  .infer (.beta (.app emptyPredicate trueRaw)),
  .infer (.symm 17),
  .infer (.trans 19 16),
  .infer (.trans 20 18),
  .infer (.refl identity),
  .infer (.eqMp 21 22),
  .infer (.disch assumedEquation 23),
  .defineType typeName [] predicate (some 24),
  .infer (.assume trueRaw),
  .infer (.disch trueRaw 26),
  .infer (.mp 27 22)]

def observe {cs : List Command} (r : Except KernelError (Result s cs)) :
    Except KernelError (Nat × Option (List RawTerm × RawTerm)) :=
  r.map fun result => (result.state.theorems.length,
    result.state.theorems.getLast?.map fun th => (th.assumptions.map Term.raw, th.conclusion.raw))

theorem completeTrace_output : observe (execute completeTrace) = .ok (29, some ([], trueRaw)) := by
  decide +kernel

theorem completeTrace_safe : completeTrace.all Command.conservative = true := by decide +kernel

theorem completeTrace_succeeds : ∃ result, execute completeTrace = .ok result := by
  have h := completeTrace_output
  cases he : execute completeTrace with
  | error e => rw [observe, he] at h; cases h
  | ok result => exact ⟨result, rfl⟩

theorem completeTrace_consistent (result : Result initial completeTrace)
    (h : execute completeTrace = .ok result) : ¬ Derivable result.state.theory [] Term.falseT :=
  execution_consistent completeTrace result h completeTrace_safe

example : observe (execute [.infer (.symm 999)]) =
    .error .invalidTheoremReference := by decide +kernel
example : observe (execute [.infer (.beta trueRaw)]) = .error .notBetaRedex := by decide +kernel
example : observe (execute [.defineType typeName [] predicate none]) =
    .error .missingNonemptyProof := by decide +kernel
example : observe (execute [.defineType typeName [] predicate (some 999)]) =
    .error .invalidTheoremReference := by decide +kernel
example : observe (execute [.addAxiom identity]) = .error .notBoolean := by decide +kernel
example : observe (execute [.defineConstant identityName identity,
    .defineConstant identityName identity]) = .error .duplicateConstant := by decide +kernel
example : observe (execute [.declareType typeName 0, .declareType typeName 1]) =
    .error .duplicateType := by decide +kernel
example : observe (execute [.addAxiom falseRaw]) =
    .ok (5, some ([], falseRaw)) := by decide +kernel
example : [Command.addAxiom falseRaw].all Command.conservative = false := by decide +kernel

end HotaruKernel.ExecutionTests
