import HotaruKernel.Execution

/-! Provenance describes construction dependencies, not authenticity of artifacts. -/
namespace HotaruKernel.Provenance

inductive Kind where
  | theoryFile
  | checkpoint
  deriving DecidableEq, Repr

structure Source where
  kind : Kind
  artifact : String
  deriving DecidableEq, Repr

inductive Trace where
  | local
  | source (source : Source)
  | join (left right : Trace)
  deriving Repr

/-- Independent specification of reachability in a construction's source history. -/
inductive Depends : Trace → Source → Prop where
  | source : Depends (.source s) s
  | left : Depends l s → Depends (.join l r) s
  | right : Depends r s → Depends (.join l r) s

/-- The history witnesses actual propagation; the cached list contains no duplicates. -/
structure Origin where
  history : Trace
  sources : List Source
  exact : ∀ s, s ∈ sources ↔ Depends history s

def Origin.local : Origin := ⟨.local, [], by
  intro s
  constructor
  · simp
  · intro h; cases h⟩

def Origin.source (s : Source) : Origin := ⟨.source s, [s], by
  intro x
  constructor
  · intro h
    obtain rfl := List.mem_singleton.mp h
    exact .source
  · intro h; cases h; simp⟩

def Origin.join (a b : Origin) : Origin :=
  ⟨.join a.history b.history, (a.sources ++ b.sources).eraseDups, by
    intro s
    simp only [List.mem_eraseDups, List.mem_append, a.exact, b.exact]
    constructor
    · rintro (h | h)
      · exact .left h
      · exact .right h
    · intro h
      cases h with
      | left h => exact Or.inl h
      | right h => exact Or.inr h⟩

theorem Origin.complete (o : Origin) : Depends o.history s → s ∈ o.sources :=
  (o.exact s).mpr

theorem Origin.absent (o : Origin) (h : s ∉ o.sources) : ¬ Depends o.history s :=
  fun hd => h (o.complete hd)

theorem Origin.kind_absent (o : Origin) (kind : Kind)
    (h : ∀ s ∈ o.sources, s.kind ≠ kind) :
    ∀ s, s.kind = kind → ¬ Depends o.history s := by
  intro s hk hd
  exact h s (o.complete hd) hk

@[simp] theorem Origin.mem_join (a b : Origin) :
    s ∈ (a.join b).sources ↔ s ∈ a.sources ∨ s ∈ b.sources := by
  simp [Origin.join]

def Origin.collect (context : Origin) (premises : List Origin) : Origin :=
  premises.foldl Origin.join context

theorem Origin.mem_collect (context : Origin) (premises : List Origin) :
    s ∈ (context.collect premises).sources ↔
      s ∈ context.sources ∨ ∃ p ∈ premises, s ∈ p.sources := by
  induction premises generalizing context with
  | nil => simp [Origin.collect]
  | cons p ps ih =>
    simp only [Origin.collect, List.foldl_cons] at *
    rw [ih]
    simp only [Origin.mem_join, List.mem_cons]
    aesop

end HotaruKernel.Provenance
