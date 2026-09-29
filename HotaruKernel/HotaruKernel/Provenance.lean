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

private def unionSources (a b : List Source) : List Source :=
  if a = [] then b
  else if b = [] then a
  else if a = b then a
  else a ++ b.filter (fun s => decide (s ∉ a))

/-! A source-set history keeps the observable dependency set without retaining
    the full derivation tree at runtime. -/
abbrev Trace := List Source

def Trace.local : Trace := []
def Trace.source (s : Source) : Trace := [s]
def Trace.join (a b : Trace) : Trace := unionSources a b

def Depends (history : Trace) (source : Source) : Prop := source ∈ history

/-- The cached source list exactly describes reachability in the history. -/
structure Origin where
  history : Trace
  sources : List Source
  exact : ∀ s, s ∈ sources ↔ Depends history s
  nodup : sources.Nodup

def Origin.local : Origin where
  history := .local
  sources := []
  exact := by simp [Depends, Trace.local]
  nodup := by simp

def Origin.source (s : Source) : Origin where
  history := .source s
  sources := [s]
  exact := by simp [Depends, Trace.source]
  nodup := by simp

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

def Origin.join (a b : Origin) : Origin :=
  if a.sources = [] then b
  else if b.sources = [] then a
  else if a.sources = b.sources then a
  else
    let sources := unionSources a.sources b.sources
    { sources := sources
      history := sources
      exact := by simp [Depends]
      nodup := nodup_unionSources a.sources b.sources a.nodup b.nodup }

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
  unfold Origin.join
  split_ifs with ha hb hab
  · simp [ha]
  · simp [hb]
  · simp [hab]
  · exact mem_unionSources a.sources b.sources s

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
