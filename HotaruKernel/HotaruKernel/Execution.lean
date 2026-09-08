import HotaruKernel.FoundationModel
import HotaruKernel.TypeDefinitionModel
import HotaruKernel.ConstantDefinitionModel
import HotaruKernel.DeclarationModels
import HotaruKernel.Sequent

namespace HotaruKernel

def Theory.HasModel (t : Theory) : Prop := ∃ p : PolymorphicModel t.signature, Models t p

theorem Theory.HasModel.consistent (h : t.HasModel) : ¬ Derivable t [] Term.falseT := by
  rintro d
  obtain ⟨p, hp⟩ := h
  let m := p.oldTypes Foundation.types
  have hf := d.sound p hp m rfl (fun a _ => Classical.choice (m.interp_nonempty a))
    (fun _ h => by cases h)
  rw [Term.eval_falseT] at hf
  cases hf

namespace Execution

structure State where
  theory : Theory
  wellFormed : theory.signature.WellFormed
  theorems : List (Thm theory)

def initial : State :=
  ⟨Foundation.theory, Foundation.wellFormed,
    [Foundation.eta, Foundation.selection, Foundation.infinity, Foundation.boolCases]⟩

def State.get (s : State) (n : Nat) : Except KernelError (Thm s.theory) :=
  match s.theorems[n]? with
  | some th => .ok th
  | none => .error .invalidTheoremReference

inductive Inference where
  | assume (p : RawTerm)
  | refl (p : RawTerm)
  | beta (p : RawTerm)
  | abs (name : String) (type : HolType) (th : Nat)
  | mkComb (left right : Nat)
  | disch (p : RawTerm) (th : Nat)
  | mp (implication antecedent : Nat)
  | symm (th : Nat)
  | trans (left right : Nat)
  | eqMp (equation premise : Nat)
  | inst (replacements : List (RawTerm × RawTerm)) (th : Nat)
  | instType (substitution : TypeSubst) (th : Nat)
  | subst (equations : List (RawTerm × Nat)) (template : RawTerm) (th : Nat)
  deriving Repr, DecidableEq

def Inference.run (s : State) : Inference → Except KernelError (Thm s.theory)
  | .assume p => Kernel.ASSUME s.theory p
  | .refl p => Kernel.REFL s.theory p
  | .beta p => Kernel.BETA_CONV s.theory p
  | .abs name a th => do Kernel.ABS s.theory name a (← s.get th)
  | .mkComb l r => do Kernel.MK_COMB s.theory (← s.get l) (← s.get r)
  | .disch p th => do Kernel.DISCH s.theory p (← s.get th)
  | .mp l r => do Kernel.MP s.theory (← s.get l) (← s.get r)
  | .symm th => do Kernel.SYM s.theory (← s.get th)
  | .trans l r => do Kernel.TRANS s.theory (← s.get l) (← s.get r)
  | .eqMp l r => do Kernel.EQ_MP s.theory (← s.get l) (← s.get r)
  | .inst rs th => do Kernel.INST s.theory rs (← s.get th)
  | .instType i th => do Kernel.INST_TYPE s.theory i (← s.get th)
  | .subst rs template th => do
    let rs ← rs.mapM (fun (v, n) => do pure (v, ← s.get n))
    Kernel.SUBST s.theory rs template (← s.get th)

inductive Command where
  | infer (rule : Inference)
  | declareType (name : QName) (arity : Nat)
  | declareConstant (name : QName) (type : HolType)
  | defineConstant (name : QName) (rhs : RawTerm)
  | defineType (name : QName) (parameters : List String) (predicate : RawTerm) (proof : Option Nat)
  | addAxiom (formula : RawTerm)
  deriving Repr, DecidableEq

def Command.conservative : Command → Bool
  | .addAxiom _ => false
  | _ => true

structure CheckedStep (s : State) (c : Command) where
  extension : TheoryExtension s.theory
  produced : List (Thm extension.target)
  preservesModels : c.conservative = true → s.theory.HasModel → extension.target.HasModel

def CheckedStep.state (step : CheckedStep s c) : State :=
  ⟨step.extension.target, step.extension.wellFormed,
    s.theorems.map (Thm.rebase step.extension.extension) ++ step.produced⟩

theorem CheckedStep.preserves_theorem (step : CheckedStep s c) (th : Thm s.theory)
    (h : th ∈ s.theorems) : th.rebase step.extension.extension ∈ step.state.theorems :=
  List.mem_append_left _ (List.mem_map.mpr ⟨th, h, rfl⟩)

theorem CheckedStep.theorem_count (step : CheckedStep s c) :
    step.state.theorems.length = s.theorems.length + step.produced.length := by
  simp only [state, List.length_append, List.length_map]

def checkStep (s : State) : (c : Command) → Except KernelError (CheckedStep s c)
  | .infer rule => do
    let th ← rule.run s
    return ⟨⟨s.theory, .refl _, s.wellFormed⟩, [th], fun _ h => h⟩
  | .declareType name arity =>
    match he : Kernel.DECLARE_TYPE s.theory name arity with
    | .error e => .error e
    | .ok ext => .ok ⟨ext, [], fun _ ⟨p, hp⟩ => by
        obtain ⟨q, hq, _⟩ := Kernel.declareType_model name arity ext he p hp
        exact ⟨q, hq⟩⟩
  | .declareConstant name a =>
    match he : Kernel.DECLARE_CONSTANT s.theory name a with
    | .error e => .error e
    | .ok ext => .ok ⟨ext, [], fun _ ⟨p, hp⟩ => by
        obtain ⟨q, hq, _⟩ := Kernel.declareConstant_model name a ext he p hp
        exact ⟨q, hq⟩⟩
  | .defineConstant name rhs => do
    let d ← Kernel.DEFINE_CONSTANT s.theory name rhs
    return ⟨d.extension, [d.definitionThm], fun _ ⟨p, hp⟩ => by
      obtain ⟨q, hq, _⟩ := d.model_extension p hp
      exact ⟨q, hq⟩⟩
  | .defineType name parameters predicate proof => do
    let proofThm ← proof.mapM s.get
    let d ← Kernel.DEFINE_TYPE s.theory name parameters predicate proofThm
    return ⟨d.extension, [d.definitionThm], fun _ ⟨p, hp⟩ => by
      obtain ⟨q, hq, _⟩ := d.model_extension p hp
      exact ⟨q, hq⟩⟩
  | .addAxiom raw => do
    let ⟨a, term, _⟩ ← check s.theory.signature [] raw
    if ha : a = .bool then
      let q : Formula s.theory.signature := cast (congrArg (Closed s.theory.signature) ha) term
      let target : Theory := ⟨s.theory.signature, q :: s.theory.axioms⟩
      let ext : TheoryExtension s.theory := ⟨target,
        ⟨.refl _, fun p hp => by
          simpa only [Term.rebase_refl] using List.mem_cons_of_mem q hp⟩, s.wellFormed⟩
      return ⟨ext, [⟨[], q, .axiom _ (List.mem_cons_self ..)⟩], fun h => by cases h⟩
    else .error .notBoolean

structure Result (s : State) (commands : List Command) where
  state : State
  extension : s.theory.Extends state.theory
  preservesModels : commands.all Command.conservative = true →
    s.theory.HasModel → state.theory.HasModel

def run (s : State) : (commands : List Command) → Except KernelError (Result s commands)
  | [] => .ok ⟨s, .refl _, fun _ h => h⟩
  | c :: cs => do
    let step ← checkStep s c
    let rest ← run step.state cs
    return ⟨rest.state, step.extension.extension.trans rest.extension, fun hsafe hp => by
      have hs : c.conservative = true ∧ cs.all Command.conservative = true := by
        simpa only [List.all_cons, Bool.and_eq_true] using hsafe
      exact rest.preservesModels hs.2 (step.preservesModels hs.1 hp)⟩

def execute (commands : List Command) : Except KernelError (Result initial commands) :=
  run initial commands

theorem successful_run_sound (s : State) (commands : List Command) (result : Result s commands)
    (_h : run s commands = .ok result) (th : Thm result.state.theory)
    (_mem : th ∈ result.state.theorems) :
    result.state.theory.Entails th.assumptions th.conclusion := th.sound

theorem successful_run_extends (s : State) (commands : List Command) (result : Result s commands)
    (_h : run s commands = .ok result) : s.theory.Extends result.state.theory := result.extension

theorem successful_run_wellFormed (s : State) (commands : List Command) (result : Result s commands)
    (_h : run s commands = .ok result) : result.state.theory.signature.WellFormed :=
  result.state.wellFormed

theorem successful_run_hasModel (s : State) (commands : List Command) (result : Result s commands)
    (_h : run s commands = .ok result) (hs : commands.all Command.conservative = true)
    (hp : s.theory.HasModel) : result.state.theory.HasModel := result.preservesModels hs hp

theorem execution_sound (commands : List Command) (result : Result initial commands)
    (h : execute commands = .ok result) (th : Thm result.state.theory)
    (hmem : th ∈ result.state.theorems) :
    result.state.theory.Entails th.assumptions th.conclusion :=
  successful_run_sound initial commands result h th hmem

theorem execution_sequents_wellFormed (commands : List Command) (result : Result initial commands)
    (_h : execute commands = .ok result) (th : Thm result.state.theory)
    (_hmem : th ∈ result.state.theorems) :
    th.sequent.WellFormed result.state.theory.signature := th.sequent_wellFormed

theorem execution_consistent (commands : List Command) (result : Result initial commands)
    (_h : execute commands = .ok result) (hs : commands.all Command.conservative = true) :
    ¬ Derivable result.state.theory [] Term.falseT :=
  (result.preservesModels hs ⟨Foundation.model, Foundation.models⟩).consistent

end Execution
end HotaruKernel
