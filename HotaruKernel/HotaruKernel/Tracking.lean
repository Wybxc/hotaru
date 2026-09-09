import HotaruKernel.Provenance

/-! Executable provenance-aware kernel. All native theorem operations use this layer. -/
namespace HotaruKernel.Tracking
open Provenance

variable {source : Source}

structure State where
  value : Execution.State
  origin : Origin

def initial : State := ⟨Execution.initial, .local⟩

structure Theorem (s : State) where
  value : Thm s.value.theory
  origin : Origin

def Theorem.mark (th : Theorem s) (source : Source) : Theorem s :=
  ⟨th.value, (th.origin.join s.origin).join (.source source)⟩

def foundation (s : State) (index : Nat) : Except KernelError (Theorem s) :=
  (s.value.get index).map fun th => ⟨th, s.origin⟩

inductive Inference (s : State) where
  | assume (p : RawTerm)
  | refl (p : RawTerm)
  | beta (p : RawTerm)
  | abs (name : String) (type : HolType) (th : Theorem s)
  | mkComb (left right : Theorem s)
  | disch (p : RawTerm) (th : Theorem s)
  | mp (implication antecedent : Theorem s)
  | symm (th : Theorem s)
  | trans (left right : Theorem s)
  | eqMp (equation premise : Theorem s)
  | inst (replacements : List (RawTerm × RawTerm)) (th : Theorem s)
  | instType (substitution : TypeSubst) (th : Theorem s)
  | subst (equations : List (RawTerm × Theorem s)) (template : RawTerm) (th : Theorem s)

/-- All theorem inputs, including every equation supplied to SUBST. -/
def Inference.premises : Inference s → List (Theorem s)
  | .assume _ | .refl _ | .beta _ => []
  | .abs _ _ th | .disch _ th | .symm th | .inst _ th | .instType _ th => [th]
  | .mkComb l r | .mp l r | .trans l r | .eqMp l r => [l, r]
  | .subst eqs _ th => th :: eqs.map Prod.snd

def Inference.runCore (s : State) : Inference s → Except KernelError (Thm s.value.theory)
  | .assume p => Kernel.ASSUME s.value.theory p
  | .refl p => Kernel.REFL s.value.theory p
  | .beta p => Kernel.BETA_CONV s.value.theory p
  | .abs n a th => Kernel.ABS s.value.theory n a th.value
  | .mkComb l r => Kernel.MK_COMB s.value.theory l.value r.value
  | .disch p th => Kernel.DISCH s.value.theory p th.value
  | .mp l r => Kernel.MP s.value.theory l.value r.value
  | .symm th => Kernel.SYM s.value.theory th.value
  | .trans l r => Kernel.TRANS s.value.theory l.value r.value
  | .eqMp l r => Kernel.EQ_MP s.value.theory l.value r.value
  | .inst rs th => Kernel.INST s.value.theory rs th.value
  | .instType i th => Kernel.INST_TYPE s.value.theory i th.value
  | .subst rs p th =>
    Kernel.SUBST s.value.theory (rs.map fun (v, e) => (v, e.value)) p th.value

def Inference.run (s : State) (rule : Inference s) : Except KernelError (Theorem s) :=
  (rule.runCore s).map fun th =>
    ⟨th, s.origin.collect (rule.premises.map Theorem.origin)⟩

/-- Uniform exact propagation theorem for every successful inference constructor. -/
theorem Inference.sources (rule : Inference s) (th : Theorem s)
    (h : rule.run s = .ok th) :
    source ∈ th.origin.sources ↔ source ∈ s.origin.sources ∨
      ∃ premise ∈ rule.premises, source ∈ premise.origin.sources := by
  unfold run at h
  cases hr : rule.runCore s <;> simp only [hr, Except.map] at h
  · cases h
  · cases h
    simp [Origin.mem_collect]

theorem Inference.sound (rule : Inference s) (th : Theorem s)
    (_h : rule.run s = .ok th) :
    s.value.theory.Entails th.value.assumptions th.value.conclusion := th.value.sound

/-- The event history records precisely the context and the declared rule premises. -/
theorem Inference.dependencies (rule : Inference s) (th : Theorem s)
    (h : rule.run s = .ok th) :
    Depends th.origin.history source ↔ Depends s.origin.history source ∨
      ∃ premise ∈ rule.premises, Depends premise.origin.history source := by
  simp only [← Origin.exact]
  exact rule.sources th h

theorem Inference.premise_preserved (rule : Inference s) (th premise : Theorem s)
    (h : rule.run s = .ok th) (hp : premise ∈ rule.premises)
    (hd : Depends premise.origin.history source) : source ∈ th.origin.sources :=
  (rule.sources th h).mpr (Or.inr ⟨premise, hp, premise.origin.complete hd⟩)

theorem Inference.context_preserved (rule : Inference s) (th : Theorem s)
    (h : rule.run s = .ok th) (hd : Depends s.origin.history source) :
    source ∈ th.origin.sources := (rule.sources th h).mpr (Or.inl (s.origin.complete hd))

inductive Change (s : State) where
  | declareType (name : QName) (arity : Nat)
  | declareConstant (name : QName) (type : HolType)
  | defineConstant (name : QName) (rhs : RawTerm)
  | defineType (name : QName) (parameters : List String) (predicate : RawTerm)
      (proof : Option (Theorem s))
  | addAxiom (formula : RawTerm)
  | mark (source : Source)

def Change.premises : Change s → List (Theorem s)
  | .defineType _ _ _ proof => proof.toList
  | _ => []

def Change.introduced : Change s → Origin
  | .mark source => .source source
  | _ => .local

structure CoreExtension (s : State) where
  data : TheoryExtension s.value.theory
  produced : Option (Thm data.target)

def Change.runCore (s : State) : Change s → Except KernelError (CoreExtension s)
  | .declareType n arity => do
    let e ← Kernel.DECLARE_TYPE s.value.theory n arity
    return ⟨e, none⟩
  | .declareConstant n a => do
    let e ← Kernel.DECLARE_CONSTANT s.value.theory n a
    return ⟨e, none⟩
  | .defineConstant n rhs => do
    let d ← Kernel.DEFINE_CONSTANT s.value.theory n rhs
    return ⟨d.extension, some d.definitionThm⟩
  | .defineType n params p proof => do
    let d ← Kernel.DEFINE_TYPE s.value.theory n params p (proof.map Theorem.value)
    return ⟨d.extension, some d.definitionThm⟩
  | .addAxiom p => do
    let step ← Execution.checkStep s.value (.addAxiom p)
    return ⟨step.extension, step.produced.head?⟩
  | .mark _ => .ok ⟨⟨s.value.theory, .refl _, s.value.wellFormed⟩, none⟩

structure Extension (s : State) where
  core : CoreExtension s
  origin : Origin

def Change.run (s : State) (change : Change s) : Except KernelError (Extension s) :=
  (change.runCore s).map fun e =>
    ⟨e, (s.origin.collect (change.premises.map Theorem.origin)).join change.introduced⟩

def Extension.state (e : Extension s) : State :=
  ⟨⟨e.core.data.target, e.core.data.wellFormed,
      s.value.theorems.map (Thm.rebase e.core.data.extension)⟩, e.origin⟩

def Extension.theorem (e : Extension s) : Option (Theorem e.state) :=
  e.core.produced.map fun th => ⟨th, e.origin⟩

def Extension.rebase (e : Extension s) (th : Theorem s) : Theorem e.state :=
  ⟨th.value.rebase e.core.data.extension, th.origin.join e.origin⟩

theorem Change.sources (change : Change s) (e : Extension s)
    (h : change.run s = .ok e) :
    source ∈ e.state.origin.sources ↔
      (source ∈ s.origin.sources ∨
        ∃ premise ∈ change.premises, source ∈ premise.origin.sources) ∨
      source ∈ change.introduced.sources := by
  unfold run at h
  cases hr : change.runCore s <;> simp only [hr, Except.map] at h
  · cases h
  · cases h
    simp [Extension.state, Origin.mem_collect]

theorem Extension.produced_sources (e : Extension s) (th : Theorem e.state)
    (h : e.theorem = some th) : th.origin.sources = e.state.origin.sources := by
  unfold Extension.theorem at h
  cases hp : e.core.produced <;> simp only [hp, Option.map] at h
  · cases h
  · cases h
    rfl

theorem Change.context_preserved (change : Change s) (e : Extension s)
    (h : change.run s = .ok e) (hd : Depends s.origin.history source) :
    source ∈ e.state.origin.sources :=
  (change.sources e h).mpr (Or.inl (Or.inl (s.origin.complete hd)))

theorem Change.premise_preserved (change : Change s) (e : Extension s) (premise : Theorem s)
    (h : change.run s = .ok e) (hp : premise ∈ change.premises)
    (hd : Depends premise.origin.history source) : source ∈ e.state.origin.sources :=
  (change.sources e h).mpr (Or.inl (Or.inr ⟨premise, hp, premise.origin.complete hd⟩))

theorem Extension.rebase_sources (e : Extension s) (th : Theorem s) :
    source ∈ (e.rebase th).origin.sources ↔
      source ∈ th.origin.sources ∨ source ∈ e.state.origin.sources :=
  Origin.mem_join _ _

theorem Theorem.mark_sources (th : Theorem s) (src : Source) :
    source ∈ (th.mark src).origin.sources ↔
      (source ∈ th.origin.sources ∨ source ∈ s.origin.sources) ∨ source = src := by
  simp [mark, Origin.source]

/-- Reachable source events cannot be omitted from a theorem's reported sources. -/
theorem Theorem.complete (th : Theorem s) :
    Depends th.origin.history source → source ∈ th.origin.sources := th.origin.complete

theorem Theorem.kind_absent (th : Theorem s) (kind : Kind)
    (h : ∀ src ∈ th.origin.sources, src.kind ≠ kind) :
    ∀ src, src.kind = kind → ¬ Depends th.origin.history src :=
  th.origin.kind_absent kind h

theorem State.complete (s : State) :
    Depends s.origin.history source → source ∈ s.origin.sources := s.origin.complete

end HotaruKernel.Tracking
