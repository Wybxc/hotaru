import HotaruKernel.Semantics

namespace HotaruKernel

variable {ctx : List HolType}

structure Theory where
  signature : Signature
  axioms : List (Formula signature) := []

def Models (t : Theory) (m : Model t.signature) : Prop :=
  ∀ f, Satisfies m f t.axioms

def Theory.Entails (t : Theory) (hs : List (Formula t.signature))
    (c : Formula t.signature) : Prop :=
  ∀ (m : Model t.signature), Models t m →
    ∀ f, Satisfies m f hs → c.eval m f BoundEnv.nil = true

inductive Derivable (t : Theory) : List (Formula t.signature) → Formula t.signature → Prop where
  | axiom (p : Formula t.signature) (h : p ∈ t.axioms) : Derivable t [] p
  | assume (p : Formula t.signature) : Derivable t [p] p
  | refl (x : Closed t.signature a) : Derivable t [] (.equal x x)
  | beta (valid : t.signature.validType a = true)
      (b : Term t.signature [a] c) (x : Closed t.signature a) :
      Derivable t [] (.equal (.app (.lam valid b) x) (b.open x))
  | abs {hs : List (Formula t.signature)} {l r : Closed t.signature b}
      (n : String) (a : HolType) (valid : t.signature.validType a = true)
      (fresh : ∀ p ∈ hs, (n, a) ∉ p.freeVars) :
      Derivable t hs (.equal l r) →
      Derivable t hs (.equal (l.abstract n a valid) (r.abstract n a valid))
  | mkComb {hs ks : List (Formula t.signature)}
      {f g : Closed t.signature (.fn a b)} {x y : Closed t.signature a} :
      Derivable t hs (.equal f g) → Derivable t ks (.equal x y) →
      Derivable t (hs ++ ks) (.equal (.app f x) (.app g y))

theorem eval_equal_true (l r : Term s ctx a) (m : Model s) (f : FreeEnv m)
    (e : BoundEnv m ctx) :
    (Term.equal l r).eval m f e = true ↔ l.eval m f e = r.eval m f e := by
  exact Iff.of_eq (@decide_eq_true_eq (l.eval m f e = r.eval m f e)
    (Classical.propDecidable _))

theorem Derivable.sound {t : Theory} {hs : List (Formula t.signature)}
    {c : Formula t.signature} (d : Derivable t hs c) : t.Entails hs c := by
  intro m hm
  induction d with
  | «axiom» p hp => exact fun f _ => hm f p hp
  | assume p => exact fun _ h => h p (by simp)
  | refl x =>
    intro f _
    exact (eval_equal_true _ _ _ _ _).mpr rfl
  | beta valid b x =>
    intro f _
    apply (eval_equal_true _ _ _ _ _).mpr
    exact (b.eval_open x m f BoundEnv.nil).symm
  | @abs b hs l r n a valid fresh d ih =>
    intro f h
    apply (eval_equal_true _ _ _ _ _).mpr
    funext x
    change (l.close n a).eval m f (BoundEnv.nil.cons x) =
      (r.close n a).eval m f (BoundEnv.nil.cons x)
    rw [Term.eval_close, Term.eval_close]
    apply (eval_equal_true _ _ _ _ _).mp
    apply ih
    intro p hp
    rw [p.eval_set_of_not_free m f BoundEnv.nil n a x (fresh p hp)]
    exact h p hp
  | mkComb df dx ihf ihx =>
    intro f h
    have hf := (eval_equal_true _ _ _ _ _).mp
      (ihf f (fun p hp => h p (List.mem_append_left _ hp)))
    have hx := (eval_equal_true _ _ _ _ _).mp
      (ihx f (fun p hp => h p (List.mem_append_right _ hp)))
    apply (eval_equal_true _ _ _ _ _).mpr
    simp only [Term.eval, hf, hx]

end HotaruKernel
