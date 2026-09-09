import HotaruKernelFFI

namespace HotaruKernel.ProvenanceTests
open Provenance

def contextSource : Source := ⟨.theoryFile, "context"⟩
def firstSource : Source := ⟨.theoryFile, "proof"⟩
def secondSource : Source := ⟨.checkpoint, "proof"⟩
def markedStep := Execution.checkStep Execution.initial (.mark contextSource)
def theory : Theory := { Foundation.theory with origin := .source contextSource }
def p : RawTerm := .fvar "p" .bool
def q : RawTerm := .fvar "q" .bool

def substSources : Except KernelError (List Source) := do
  let l ← Kernel.REFL theory p
  let r ← Kernel.REFL theory p
  let h ← Kernel.ASSUME theory p
  let th ← Kernel.SUBST theory [(p, l.mark firstSource), (q, r.mark secondSource)] p h
  return th.origin.sources

example : substSources = .ok [contextSource, firstSource, secondSource] := by
  decide +kernel

example : (Kernel.REFL theory p).map (fun th => th.origin.sources) =
    .ok [contextSource] := by decide +kernel

example : (do
    let step ← markedStep
    let th ← step.state.get 0
    pure th.origin.sources) = .ok [contextSource] := by decide +kernel

def migratedSources : Except KernelError (List Source) := do
  let th ← Kernel.REFL theory p
  let e ← Kernel.MARK_THEORY theory secondSource
  return (th.mark firstSource |>.rebase e.extension).origin.sources

example : migratedSources = .ok [contextSource, firstSource, secondSource] := by
  decide +kernel

def duplicateSources : Except KernelError (List Source) := do
  let th ← Kernel.REFL theory p
  return ((th.mark firstSource).mark firstSource).origin.sources

example : duplicateSources = .ok [contextSource, firstSource] := by decide +kernel

def executionSources : Except KernelError (List Source × List (List Source)) := do
  let out ← Execution.execute [
    .mark firstSource, .infer (.refl p), .mark secondSource,
    .declareType ⟨"provenance", "declared"⟩ 0, .addAxiom p]
  return (out.state.theory.origin.sources, out.state.theorems.map (fun th => th.origin.sources))

example : executionSources = .ok ([firstSource, secondSource],
    List.replicate 6 [firstSource, secondSource]) := by decide +kernel

example (_th : Thm Foundation.theory) : True := by
  fail_if_success have : Thm theory := _th
  trivial

example : FFI.source 2 "invalid" = .error 6 := by decide +kernel
example : FFI.sourcesGet #[firstSource] 1 = .error 8 := by decide +kernel
example : FFI.sourceKind secondSource = 1 := by decide +kernel
example : FFI.sourceArtifact firstSource = "proof" := by decide +kernel

/-- Every SUBST equation remains a dependency even if the template does not use it. -/
theorem subst_equation_preserved (t : Theory) (equations : List (RawTerm × Thm t))
    (template : RawTerm) (input output equation : Thm t) (target : RawTerm)
    (src : Source) (h : Kernel.SUBST t equations template input = .ok output)
    (he : (target, equation) ∈ equations) (hd : Depends equation.origin.history src) :
    src ∈ output.origin.sources :=
  (Kernel.subst_sources equations template input output h).mpr
    (Or.inr (Or.inr ⟨(target, equation), he, equation.complete hd⟩))

/-- A type definition carries its nonemptiness proof's sources into the new context. -/
theorem type_definition_preserved (t : Theory) (name : QName) (parameters : List String)
    (predicate : RawTerm) (proof : Thm t) (d : TypeDefinition t) (src : Source)
    (h : Kernel.DEFINE_TYPE t name parameters predicate (some proof) = .ok d)
    (hd : Depends proof.origin.history src) : src ∈ d.target.origin.sources :=
  (Kernel.defineType_sources name parameters predicate proof d h).mpr
    (Or.inr (proof.complete hd))

end HotaruKernel.ProvenanceTests
