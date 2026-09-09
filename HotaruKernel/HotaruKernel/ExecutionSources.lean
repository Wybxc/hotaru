import HotaruKernel.Execution
import HotaruKernel.KernelSources

namespace HotaruKernel.Execution
open Provenance

variable {src : Source}

theorem checkStep_context_preserved (s : State) (c : Command) (step : CheckedStep s c)
    (h : checkStep s c = .ok step) (hs : src ∈ s.theory.origin.sources) :
    src ∈ step.state.theory.origin.sources := by
  cases c <;> simp only [checkStep, Kernel.DECLARE_TYPE, Kernel.DECLARE_CONSTANT] at h
  all_goals source_check h
  all_goals simp only [CheckedStep.state, ConstantDefinition.extension,
    ConstantDefinition.target, TypeDefinition.extension, TypeDefinition.target,
    Origin.mem_join, hs, true_or]
  all_goals
    rename_i he
    source_check he
    exact hs

theorem addAxiom_origin (s : State) (p : RawTerm) (step : CheckedStep s (.addAxiom p))
    (h : checkStep s (.addAxiom p) = .ok step) :
    step.state.theory.origin = s.theory.origin ∧
      ∀ th ∈ step.produced, th.origin = s.theory.origin := by
  simp only [checkStep] at h
  source_check h
  simp [CheckedStep.state]

theorem mark_origin (s : State) (source : Source) (step : CheckedStep s (.mark source))
    (h : checkStep s (.mark source) = .ok step) :
    step.state.theory.origin = s.theory.origin.join (.source source) := by
  cases h
  rfl

theorem run_context_preserved (s : State) (commands : List Command) (out : Result s commands)
    (h : run s commands = .ok out) (hs : src ∈ s.theory.origin.sources) :
    src ∈ out.state.theory.origin.sources := by
  induction commands generalizing s with
  | nil => cases h; exact hs
  | cons c cs ih =>
    simp only [run] at h
    cases hc : checkStep s c with
    | error e => simp [hc, bind, Except.bind] at h
    | ok step =>
      cases hr : run step.state cs with
      | error e => simp [hc, hr, bind, Except.bind] at h
      | ok rest =>
        simp only [hc, hr, bind, Except.bind, pure, Except.pure] at h
        cases h
        exact ih step.state rest hr (checkStep_context_preserved s c step hc hs)

end HotaruKernel.Execution
