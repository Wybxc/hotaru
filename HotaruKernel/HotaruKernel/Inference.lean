import HotaruKernel.Substitution
import HotaruKernel.Equality

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
  | disch {hs : List (Formula t.signature)} {q : Formula t.signature}
      (p : Formula t.signature) : Derivable t hs q →
      Derivable t (hs.filter (fun h => decide (h ≠ p))) (.imp p q)
  | mp {hs ks : List (Formula t.signature)} {p q : Formula t.signature} :
      Derivable t hs (.imp p q) → Derivable t ks p → Derivable t (hs ++ ks) q
  | symm {hs : List (Formula t.signature)} {l r : Closed t.signature a} :
      Derivable t hs (.equal l r) → Derivable t hs (.equal r l)
  | trans {hs ks : List (Formula t.signature)} {l r u : Closed t.signature a} :
      Derivable t hs (.equal l r) → Derivable t ks (.equal r u) →
      Derivable t (hs ++ ks) (.equal l u)
  | eqMp {hs ks : List (Formula t.signature)} {p q : Formula t.signature} :
      Derivable t hs (.equal p q) → Derivable t ks p → Derivable t (hs ++ ks) q
  | inst {hs : List (Formula t.signature)} {p : Formula t.signature}
      (rs : Substitution t.signature) : Derivable t hs p →
      Derivable t (hs.map rs.apply) (rs.apply p)
  | subst {hs : List (Formula t.signature)} (rs : List (RewriteEntry t.signature))
      (template : Formula t.signature)
      (eqs : ∀ r ∈ rs, Derivable t r.hypotheses (.equal r.left r.right)) :
      Derivable t hs ((rewriteSubst rs false).apply template) →
      Derivable t (rewriteHypotheses rs ++ hs) ((rewriteSubst rs true).apply template)

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
  | disch p d ih =>
    intro f h
    by_cases hp : p.eval m f BoundEnv.nil = true
    · have hq := ih f (by
        intro q hq
        by_cases he : q = p
        · simpa [he] using hp
        · exact h q (List.mem_filter.mpr ⟨hq, by simp [he]⟩))
      simp [Term.eval, hp, hq]
    · have hp' : p.eval m f BoundEnv.nil = false := Bool.eq_false_iff.mpr hp
      simp [Term.eval, hp']
  | mp dp dq ihp ihq =>
    intro f h
    have hp := ihp f (fun p hp => h p (List.mem_append_left _ hp))
    have hq := ihq f (fun p hp => h p (List.mem_append_right _ hp))
    simpa [Term.eval, hq] using hp
  | symm d ih =>
    intro f h
    exact (eval_equal_true _ _ _ _ _).mpr ((eval_equal_true _ _ _ _ _).mp (ih f h)).symm
  | trans dl dr ihl ihr =>
    intro f h
    have hl := (eval_equal_true _ _ _ _ _).mp
      (ihl f (fun p hp => h p (List.mem_append_left _ hp)))
    have hr := (eval_equal_true _ _ _ _ _).mp
      (ihr f (fun p hp => h p (List.mem_append_right _ hp)))
    exact (eval_equal_true _ _ _ _ _).mpr (hl.trans hr)
  | eqMp dp dq ihp ihq =>
    intro f h
    have hp := (eval_equal_true _ _ _ _ _).mp
      (ihp f (fun p hp => h p (List.mem_append_left _ hp)))
    have hq := ihq f (fun p hp => h p (List.mem_append_right _ hp))
    exact hp.symm.trans hq
  | inst rs d ih =>
    intro f h
    rw [Substitution.eval_apply]
    apply ih
    intro p hp
    rw [← Substitution.eval_apply]
    exact h _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
  | subst rs template eqs d iheqs ih =>
    intro f h
    have he : ∀ r ∈ rs,
        r.left.eval m f BoundEnv.nil = r.right.eval m f BoundEnv.nil := by
      intro r hr
      apply (eval_equal_true _ _ _ _ _).mp
      apply iheqs r hr f
      intro p hp
      exact h p (List.mem_append_left _ (List.mem_flatMap.mpr ⟨r, hr, hp⟩))
    rw [← rewrite_eval rs template m f he]
    exact ih f (fun p hp => h p (List.mem_append_right _ hp))

end HotaruKernel
