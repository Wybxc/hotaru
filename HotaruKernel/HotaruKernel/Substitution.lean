import HotaruKernel.Semantics

namespace HotaruKernel

structure Replacement (s : Signature) where
  type : HolType
  name : String
  value : Closed s type

abbrev Substitution (s : Signature) := List (Replacement s)

def Substitution.lookup : Substitution s → FreeSubst s []
  | [] => fun n a h => .fvar n a h
  | r :: rs => fun n a h =>
      if ht : r.type = a then
        if r.name = n then ht ▸ r.value else Substitution.lookup rs n a h
      else Substitution.lookup rs n a h

def Substitution.apply (rs : Substitution s) (t : Closed s a) : Closed s a :=
  t.substFree rs.lookup (fun v => v)

noncomputable def Substitution.valuation (rs : Substitution s) (m : Model s)
    (f : FreeEnv m) : FreeEnv m := fun a n =>
  if h : s.validType a = true then (rs.lookup n a h).eval m f BoundEnv.nil else f a n

theorem Substitution.eval_apply (rs : Substitution s) (t : Closed s a)
    (m : Model s) (f : FreeEnv m) :
    (rs.apply t).eval m f BoundEnv.nil = t.eval m (rs.valuation m f) BoundEnv.nil := by
  apply t.eval_substFree
  · intro n a h
    simp [valuation, h]
  · intro a v
    cases v

structure RewriteEntry (s : Signature) where
  type : HolType
  name : String
  left : Closed s type
  right : Closed s type
  hypotheses : List (Formula s)

def RewriteEntry.replacement (r : RewriteEntry s) (right : Bool) : Replacement s :=
  ⟨r.type, r.name, if right then r.right else r.left⟩

def rewriteSubst (rs : List (RewriteEntry s)) (right : Bool) : Substitution s :=
  rs.map (fun r => r.replacement right)

def rewriteHypotheses (rs : List (RewriteEntry s)) : List (Formula s) :=
  rs.flatMap RewriteEntry.hypotheses

theorem rewrite_lookup_eval (rs : List (RewriteEntry s)) (m : Model s) (f : FreeEnv m)
    (h : ∀ r ∈ rs, r.left.eval m f BoundEnv.nil = r.right.eval m f BoundEnv.nil)
    (n : String) (a : HolType) (hv : s.validType a = true) :
    ((rewriteSubst rs false).lookup n a hv).eval m f BoundEnv.nil =
      ((rewriteSubst rs true).lookup n a hv).eval m f BoundEnv.nil := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have hr := h r (List.mem_cons_self ..)
    have ht := ih (fun r hr => h r (List.mem_cons_of_mem _ hr))
    simp only [rewriteSubst, List.map_cons, Substitution.lookup, RewriteEntry.replacement,
      Bool.false_eq_true, ↓reduceIte]
    by_cases ha : r.type = a
    · subst a
      by_cases hn : r.name = n
      · simpa [hn] using hr
      · simpa [hn] using ht
    · simpa [ha] using ht

theorem rewrite_eval (rs : List (RewriteEntry s)) (t : Closed s a)
    (m : Model s) (f : FreeEnv m)
    (h : ∀ r ∈ rs, r.left.eval m f BoundEnv.nil = r.right.eval m f BoundEnv.nil) :
    ((rewriteSubst rs false).apply t).eval m f BoundEnv.nil =
      ((rewriteSubst rs true).apply t).eval m f BoundEnv.nil := by
  rw [Substitution.eval_apply, Substitution.eval_apply]
  apply t.eval_free_congr
  intro n a _
  by_cases hv : s.validType a = true
  · simpa [Substitution.valuation, hv] using rewrite_lookup_eval rs m f h n a hv
  · simp [Substitution.valuation, hv]

end HotaruKernel
