import HotaruKernel.SubstitutionLemmas
import HotaruKernel.LogicalEquality
import HotaruKernel.TypeInstantiationSemantics
import HotaruKernel.BooleanFoundation

import HotaruKernel.Provenance

namespace HotaruKernel

variable {ctx : List HolType}

structure Theory where
  signature : Signature
  axioms : List (Formula signature) := []
  origin : Provenance.Origin := .local

def Models (t : Theory) (p : PolymorphicModel t.signature) : Prop :=
  ∀ (m : TypeModel) (hm : m.typeOp = p.typeOp) f, Satisfies (p.atTypes m hm) f t.axioms

def Theory.Entails (t : Theory) (hs : List (Formula t.signature))
    (c : Formula t.signature) : Prop :=
  ∀ (p : PolymorphicModel t.signature), Models t p →
    ∀ (m : TypeModel) (hm : m.typeOp = p.typeOp) f,
      Satisfies (p.atTypes m hm) f hs → c.eval (p.atTypes m hm) f BoundEnv.nil = true

inductive Derivable (t : Theory) : List (Formula t.signature) → Formula t.signature → Prop where
  | context {hs ks : List (Formula t.signature)} {p : Formula t.signature}
      (same : ∀ q, q ∈ hs ↔ q ∈ ks) : Derivable t hs p → Derivable t ks p
  | conversion {hs : List (Formula t.signature)} {p q : Formula t.signature}
      (h : p.Equivalent q) : Derivable t hs p → Derivable t hs q
  | axiom (p : Formula t.signature) (h : p ∈ t.axioms) : Derivable t [] p
  | booleanAxiom {p : Formula t.signature} (h : BooleanAxiom t.signature p) : Derivable t [] p
  | assume (p : Formula t.signature) : Derivable t [p] p
  | refl (x : Closed t.signature a) : Derivable t [] (.equal x x)
  | beta (valid : t.signature.validType a = true)
      (b : Term t.signature [a] c) (x : Closed t.signature a) :
      Derivable t [] (.equal (.app (.lam valid b) x) (b.open x))
  | holEquality (a : HolType) (valid : t.signature.validType a = true)
      (l r : Closed t.signature a) :
      Derivable t [] (.equal (Term.holEquality a valid l r) (.equal l r))
  | abs {hs : List (Formula t.signature)} {l r : Closed t.signature b}
      (n : String) (a : HolType) (valid : t.signature.validType a = true)
      (fresh : ∀ p ∈ hs, (n, a) ∉ p.freeVars) :
      Derivable t hs (.equal l r) →
      Derivable t hs (.equal (l.abstract n a valid) (r.abstract n a valid))
  | disch {hs : List (Formula t.signature)} {q : Formula t.signature}
      (p : Formula t.signature) : Derivable t hs q →
      Derivable t (hs.filter (fun h => decide (¬ h.Equivalent p))) (.imp p q)
  | mp {hs ks : List (Formula t.signature)} {p q : Formula t.signature} :
      Derivable t hs (.imp p q) → Derivable t ks p → Derivable t (hs ++ ks) q
  | instType {hs : List (Formula t.signature)} {p : Formula t.signature}
      (i : TypeSubst) (hi : i.Valid t.signature) : Derivable t hs p →
      Derivable t (hs.map (Term.instType i hi)) (p.instType i hi)
  | subst {hs : List (Formula t.signature)} (rs : List (RewriteEntry t.signature))
      (template : Formula t.signature)
      (eqs : ∀ r ∈ rs, Derivable t r.hypotheses (.equal r.left r.right)) :
      Derivable t hs ((rewriteSubst rs false).apply template) →
      Derivable t (rewriteHypotheses rs ++ hs) ((rewriteSubst rs true).apply template)

theorem Derivable.singleSubst {t : Theory} {hs : List (Formula t.signature)}
    (entry : RewriteEntry t.signature) (template : Formula t.signature)
    (de : Derivable t entry.hypotheses (.equal entry.left entry.right))
    (dp : Derivable t hs (Substitution.apply [entry.replacement false] template)) :
    Derivable t (entry.hypotheses ++ hs)
      (Substitution.apply [entry.replacement true] template) := by
  have eqs : ∀ r ∈ [entry], Derivable t r.hypotheses (.equal r.left r.right) := by
    intro r hr
    have hr' : r = entry := List.mem_singleton.mp hr
    subst r
    exact de
  simpa [rewriteSubst, rewriteHypotheses] using
    Derivable.subst (t := t) [entry] template eqs dp

theorem Derivable.symm {t : Theory} {hs : List (Formula t.signature)}
    {l r : Closed t.signature a} (de : Derivable t hs (.equal l r)) :
    Derivable t hs (.equal r l) := by
  let entry : RewriteEntry t.signature := ⟨a, freshName l.freeVars, l, r, hs⟩
  have fresh : (entry.name, entry.type) ∉ l.freeVars := freshName_not_mem _ _
  have hl := Substitution.apply_fresh l (entry.replacement false) fresh
  have hr := Substitution.apply_fresh l (entry.replacement true) fresh
  let v : Closed t.signature a := .fvar entry.name a (l.validType (fun _ h => by cases h))
  have hv (side : Bool) : Substitution.apply [entry.replacement side] v =
      if side then r else l := Substitution.apply_single_variable _ _
  have dp : Derivable t [] (Substitution.apply [entry.replacement false] (.equal v l)) := by
    rw [Substitution.apply_equal, hv, hl]
    exact .refl l
  have d := Derivable.singleSubst entry (.equal v l) de dp
  simpa only [Substitution.apply_equal, hv, hr, Bool.true_eq_false, ite_true,
    List.append_nil] using d

theorem Derivable.eqMp {t : Theory} {hs ks : List (Formula t.signature)}
    {p q : Formula t.signature} (de : Derivable t hs (.equal p q))
    (dp : Derivable t ks p) : Derivable t (hs ++ ks) q := by
  let entry : RewriteEntry t.signature := ⟨.bool, "p", p, q, hs⟩
  have eqs : ∀ r ∈ [entry], Derivable t r.hypotheses (.equal r.left r.right) := by
    intro r hr
    have hr' : r = entry := List.mem_singleton.mp hr
    subst r
    exact de
  have d := Derivable.subst (t := t) (hs := ks) [entry]
    (.fvar "p" .bool (by simp [Signature.validType])) eqs
  simpa [entry, rewriteSubst, rewriteHypotheses, RewriteEntry.replacement,
    Substitution.apply, Substitution.lookup, Term.substFree] using d dp

theorem Derivable.trans {t : Theory} {hs ks : List (Formula t.signature)}
    {l r u : Closed t.signature a} (dl : Derivable t hs (.equal l r))
    (dr : Derivable t ks (.equal r u)) : Derivable t (hs ++ ks) (.equal l u) := by
  let entry : RewriteEntry t.signature := ⟨a, freshName l.freeVars, r, u, ks⟩
  have fresh : (entry.name, entry.type) ∉ l.freeVars := freshName_not_mem _ _
  have hl := Substitution.apply_fresh l (entry.replacement false) fresh
  have hr := Substitution.apply_fresh l (entry.replacement true) fresh
  let v : Closed t.signature a := .fvar entry.name a (l.validType (fun _ h => by cases h))
  have hv (side : Bool) : Substitution.apply [entry.replacement side] v =
      if side then u else r := Substitution.apply_single_variable _ _
  have dp : Derivable t hs (Substitution.apply [entry.replacement false] (.equal l v)) := by
    rw [Substitution.apply_equal, hv, hl]
    exact dl
  have d := Derivable.singleSubst entry (.equal l v) dr dp
  have d' : Derivable t (ks ++ hs) (.equal l u) := by
    simpa only [Substitution.apply_equal, hv, hr, ite_true] using d
  exact .context (fun _ => by simp only [List.mem_append, or_comm]) d'

theorem Derivable.congrFun {t : Theory} {hs : List (Formula t.signature)}
    {f g : Closed t.signature (.fn a b)} (de : Derivable t hs (.equal f g))
    (x : Closed t.signature a) : Derivable t hs (.equal (.app f x) (.app g x)) := by
  let base : Closed t.signature b := .app f x
  let entry : RewriteEntry t.signature := ⟨.fn a b, freshName base.freeVars, f, g, hs⟩
  have fresh : (entry.name, entry.type) ∉ base.freeVars := freshName_not_mem _ _
  have hb (side : Bool) := Substitution.apply_fresh base (entry.replacement side) fresh
  have hx (side : Bool) := Substitution.apply_fresh x (entry.replacement side)
    (fun h => fresh (List.mem_append_right _ h))
  let v : Closed t.signature (.fn a b) :=
    .fvar entry.name _ (f.validType (fun _ h => by cases h))
  have hv (side : Bool) : Substitution.apply [entry.replacement side] v =
      if side then g else f := Substitution.apply_single_variable _ _
  have dp : Derivable t []
      (Substitution.apply [entry.replacement false] (.equal base (.app v x))) := by
    rw [Substitution.apply_equal, hb, Substitution.apply_app, hv, hx]
    exact .refl base
  have d := Derivable.singleSubst entry (.equal base (.app v x)) de dp
  simpa only [Substitution.apply_equal, hb, Substitution.apply_app, hv, hx,
    ite_true, List.append_nil] using d

theorem Derivable.congrArg {t : Theory} {hs : List (Formula t.signature)}
    (f : Closed t.signature (.fn a b)) {x y : Closed t.signature a}
    (de : Derivable t hs (.equal x y)) : Derivable t hs (.equal (.app f x) (.app f y)) := by
  let base : Closed t.signature b := .app f x
  let entry : RewriteEntry t.signature := ⟨a, freshName base.freeVars, x, y, hs⟩
  have fresh : (entry.name, entry.type) ∉ base.freeVars := freshName_not_mem _ _
  have hb (side : Bool) := Substitution.apply_fresh base (entry.replacement side) fresh
  have hf (side : Bool) := Substitution.apply_fresh f (entry.replacement side)
    (fun h => fresh (List.mem_append_left _ h))
  let v : Closed t.signature a := .fvar entry.name _ (x.validType (fun _ h => by cases h))
  have hv (side : Bool) : Substitution.apply [entry.replacement side] v =
      if side then y else x := Substitution.apply_single_variable _ _
  have dp : Derivable t []
      (Substitution.apply [entry.replacement false] (.equal base (.app f v))) := by
    rw [Substitution.apply_equal, hb, Substitution.apply_app, hv, hf]
    exact .refl base
  have d := Derivable.singleSubst entry (.equal base (.app f v)) de dp
  simpa only [Substitution.apply_equal, hb, Substitution.apply_app, hv, hf,
    ite_true, List.append_nil] using d

theorem Derivable.mkComb {t : Theory} {hs ks : List (Formula t.signature)}
    {f g : Closed t.signature (.fn a b)} {x y : Closed t.signature a}
    (df : Derivable t hs (.equal f g)) (dx : Derivable t ks (.equal x y)) :
    Derivable t (hs ++ ks) (.equal (.app f x) (.app g y)) :=
  (df.congrFun x).trans (Derivable.congrArg g dx)

theorem eval_equal_true (l r : Term s ctx a) (m : Model s) (f : FreeEnv m)
    (e : BoundEnv m ctx) :
    (Term.equal l r).eval m f e = true ↔ l.eval m f e = r.eval m f e := by
  exact Iff.of_eq (@decide_eq_true_eq (l.eval m f e = r.eval m f e)
    (Classical.propDecidable _))

theorem Derivable.sound {t : Theory} {hs : List (Formula t.signature)}
    {c : Formula t.signature} (d : Derivable t hs c) : t.Entails hs c := by
  intro poly hpoly
  induction d with
  | context same d ih =>
    intro types htypes f h
    exact ih types htypes f (fun q hq => h q ((same q).mp hq))
  | conversion he d ih =>
    intro types htypes f h
    exact (he.eval (poly.atTypes types htypes) f BoundEnv.nil).symm.trans
      (ih types htypes f h)
  | «axiom» p hp => exact fun m hm f _ => hpoly m hm f p hp
  | booleanAxiom h => exact fun m hm f _ => h.sound (poly.atTypes m hm) f
  | assume p => exact fun _ _ _ h => h p (by simp)
  | refl x =>
    intro types htypes f _
    exact (eval_equal_true _ _ _ _ _).mpr rfl
  | beta valid b x =>
    intro types htypes f _
    let m := poly.atTypes types htypes
    apply (eval_equal_true _ _ _ _ _).mpr
    exact (b.eval_open x m f BoundEnv.nil).symm
  | holEquality a valid l r =>
    intro types htypes f _
    let m := poly.atTypes types htypes
    apply (eval_equal_true _ _ _ _ _).mpr
    exact Term.eval_holEquality a valid l r m f
  | @abs b hs l r n a valid fresh d ih =>
    intro types htypes f h
    let m := poly.atTypes types htypes
    have ih := ih types htypes
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
  | disch p d ih =>
    intro types htypes f h
    have ih := ih types htypes
    by_cases hp : p.eval (poly.atTypes types htypes) f BoundEnv.nil = true
    · have hq := ih f (by
        intro q hq
        by_cases he : q.Equivalent p
        · exact (he.eval (poly.atTypes types htypes) f BoundEnv.nil).trans hp
        · exact h q (List.mem_filter.mpr ⟨hq, by simp [he]⟩))
      simp [Term.eval, hp, hq]
    · have hp' : p.eval (poly.atTypes types htypes) f BoundEnv.nil = false :=
        Bool.eq_false_iff.mpr hp
      simp [Term.eval, hp']
  | mp dp dq ihp ihq =>
    intro types htypes f h
    have ihp := ihp types htypes
    have ihq := ihq types htypes
    have hp := ihp f (fun p hp => h p (List.mem_append_left _ hp))
    have hq := ihq f (fun p hp => h p (List.mem_append_right _ hp))
    simpa [Term.eval, hq] using hp
  | @instType hs p i hi d ih =>
    intro types htypes f h
    apply (Formula.eval_instType p i hi poly types htypes f).trans
    apply ih (types.instantiate i) htypes
    intro p hp
    exact (Formula.eval_instType p i hi poly types htypes f).symm.trans
      (h _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
  | subst rs template eqs d iheqs ih =>
    intro types htypes f h
    let m := poly.atTypes types htypes
    have ih := ih types htypes
    have he : ∀ r ∈ rs,
        r.left.eval m f BoundEnv.nil = r.right.eval m f BoundEnv.nil := by
      intro r hr
      apply (eval_equal_true _ _ _ _ _).mp
      apply iheqs r hr types htypes f
      intro p hp
      exact h p (List.mem_append_left _ (List.mem_flatMap.mpr ⟨r, hr, hp⟩))
    rw [← rewrite_eval rs template m f he]
    exact ih f (fun p hp => h p (List.mem_append_right _ hp))

end HotaruKernel
