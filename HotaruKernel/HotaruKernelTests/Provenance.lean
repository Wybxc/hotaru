import HotaruKernelFFI

namespace HotaruKernel.ProvenanceTests
open Provenance Tracking

def contextSource : Source := ⟨.theoryFile, "context"⟩
def firstSource : Source := ⟨.theoryFile, "proof"⟩
def secondSource : Source := ⟨.checkpoint, "proof"⟩
def state : State := ⟨Execution.initial, .source contextSource⟩
def p : RawTerm := .fvar "p" .bool
def q : RawTerm := .fvar "q" .bool

def substSources : Except KernelError (List Source) := do
  let l ← Inference.run state (.refl p)
  let r ← Inference.run state (.refl p)
  let h ← Inference.run state (.assume p)
  let th ← Inference.run state
    (.subst [(p, l.mark firstSource), (q, r.mark secondSource)] p h)
  return th.origin.sources

example : substSources = .ok [contextSource, firstSource, secondSource] := by
  decide +kernel

example : (Inference.run state (.refl p)).map (fun th => th.origin.sources) =
    .ok [contextSource] := by decide +kernel

example : (foundation state 0).map (fun th => th.origin.sources) =
    .ok [contextSource] := by decide +kernel

def migratedSources : Except KernelError (List Source) := do
  let th ← Inference.run state (.refl p)
  let e ← Change.run state (.mark secondSource)
  return (e.rebase (th.mark firstSource)).origin.sources

example : migratedSources = .ok [contextSource, firstSource, secondSource] := by
  decide +kernel

def duplicateSources : Except KernelError (List Source) := do
  let th ← Inference.run state (.refl p)
  return ((th.mark firstSource).mark firstSource).origin.sources

example : duplicateSources = .ok [contextSource, firstSource] := by decide +kernel

example : FFI.source 2 "invalid" = .error 6 := by decide +kernel
example : FFI.sourcesGet #[firstSource] 1 = .error 8 := by decide +kernel
example : FFI.sourceKind secondSource = 1 := by decide +kernel
example : FFI.sourceArtifact firstSource = "proof" := by decide +kernel

/-- Every SUBST equation remains a dependency even if the template does not use it. -/
theorem subst_equation_preserved (s : State) (equations : List (RawTerm × Theorem s))
    (template : RawTerm) (input output equation : Theorem s) (target : RawTerm)
    (src : Source)
    (h : Inference.run s (.subst equations template input) = .ok output)
    (he : (target, equation) ∈ equations) (hd : Depends equation.origin.history src) :
    src ∈ output.origin.sources := by
  apply Inference.premise_preserved _ output equation h _ hd
  simp only [Inference.premises, List.mem_cons]
  exact Or.inr (List.mem_map.mpr ⟨(target, equation), he, rfl⟩)

/-- A type definition carries its nonemptiness proof's sources into the new context. -/
theorem type_definition_preserved (s : State) (name : QName) (parameters : List String)
    (predicate : RawTerm) (proof : Theorem s) (e : Extension s) (src : Source)
    (h : Change.run s (.defineType name parameters predicate (some proof)) = .ok e)
    (hd : Depends proof.origin.history src) : src ∈ e.state.origin.sources := by
  apply Change.premise_preserved _ e proof h _ hd
  simp [Change.premises]

end HotaruKernel.ProvenanceTests
