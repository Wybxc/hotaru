import Mathlib.Data.List.Nodup
import Aesop

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

/-- The cached source list exactly describes reachability in the history. -/
structure Origin where
  history : Trace
  sources : List Source
  exact : ∀ s, s ∈ sources ↔ Depends history s
  nodup : sources.Nodup

def Origin.local : Origin where
  history := .local
  sources := []
  exact := by
    intro s
    constructor
    · simp
    · intro h; cases h
  nodup := by simp

def Origin.source (s : Source) : Origin where
  history := .source s
  sources := [s]
  exact := by
    intro x
    constructor
    · intro h
      obtain rfl := List.mem_singleton.mp h
      exact .source
    · intro h; cases h; simp
  nodup := by simp

private def unionSources (a b : List Source) : List Source :=
  if a = [] then b
  else if b = [] then a
  else if a = b then a
  else a ++ b.filter (fun s => decide (s ∉ a))

private theorem mem_unionSources (a b : List Source) (s : Source) :
    s ∈ unionSources a b ↔ s ∈ a ∨ s ∈ b := by
  unfold unionSources
  split_ifs with ha hb hab
  · simp [ha]
  · simp [hb]
  · simp [hab]
  · simp; tauto

private theorem nodup_unionSources (a b : List Source)
    (ha : a.Nodup) (hb : b.Nodup) : (unionSources a b).Nodup := by
  unfold unionSources
  split_ifs with h₁ h₂ h₃
  · exact hb
  · exact ha
  · exact ha
  · apply List.nodup_append.mpr
    refine ⟨ha, hb.filter _, ?_⟩
    intro x hx y hy hxy
    have hy' : y ∉ a := by simpa using (List.mem_filter.mp hy).2
    exact hy' (hxy ▸ hx)

def Origin.join (a b : Origin) : Origin where
  history := .join a.history b.history
  sources := unionSources a.sources b.sources
  exact := by
    intro s
    simp only [mem_unionSources, a.exact, b.exact]
    constructor
    · rintro (h | h)
      · exact .left h
      · exact .right h
    · intro h
      cases h with
      | left h => exact Or.inl h
      | right h => exact Or.inr h
  nodup := nodup_unionSources a.sources b.sources a.nodup b.nodup

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
  exact mem_unionSources a.sources b.sources s

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
