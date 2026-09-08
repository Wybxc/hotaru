import HotaruKernel.Inference
import HotaruKernel.MixedSubstitution

namespace HotaruKernel

theorem Derivable.truth (t : Theory) : Derivable t [] (HotaruKernel.truth t.signature) :=
  .refl _

theorem Derivable.eqtIntro {t : Theory} {p : Formula t.signature}
    (d : Derivable t [] p) : Derivable t [] (.equal p (HotaruKernel.truth t.signature)) := by
  have ax : Derivable t [] (impAntisym p (HotaruKernel.truth t.signature)) :=
    .booleanAxiom (.impAntisym _ _)
  exact .mp (.mp ax (.disch p (Derivable.truth t))) (.disch _ d)

theorem Derivable.instEquality {t : Theory} (rs : Substitution t.signature)
    {l r : Closed t.signature a} (d : Derivable t [] (.equal l r)) :
    Derivable t [] (.equal (rs.apply l) (rs.apply r)) := by
  induction rs generalizing a with
  | nil => simpa only [Substitution.apply_nil] using d
  | cons entry rs ih =>
    have hv := entry.value.validType (fun _ h => by cases h)
    have da := Derivable.abs entry.name entry.type hv (fun _ h => by cases h) d
    have di := ih da
    rw [Substitution.apply_abstract, Substitution.apply_abstract] at di
    have dc := Derivable.mkComb di (Derivable.refl entry.value)
    have bl := Derivable.beta (t := t) hv
      ((l.close entry.name entry.type).substFree (Substitution.lookup rs).lift (fun v => v))
      entry.value
    have br := Derivable.beta (t := t) hv
      ((r.close entry.name entry.type).substFree (Substitution.lookup rs).lift (fun v => v))
      entry.value
    rw [Substitution.apply_cons_close] at bl br
    exact (bl.symm.trans dc).trans br

theorem Substitution.apply_truth (rs : Substitution s) : rs.apply (truth s) = truth s := by
  apply Term.substFree_eq
  · intro n a hv h
    cases h
  · exact fun _ _ => rfl

theorem Derivable.instClosed {t : Theory} (rs : Substitution t.signature)
    {p : Formula t.signature} (d : Derivable t [] p) : Derivable t [] (rs.apply p) := by
  have de := Derivable.instEquality rs d.eqtIntro
  rw [Substitution.apply_truth] at de
  exact de.symm.eqMp (Derivable.truth t)

def implyList (qs : List (Formula s)) (p : Formula s) : Formula s :=
  qs.foldr Term.imp p

def residual (qs hs : List (Formula s)) : List (Formula s) :=
  qs.foldr (fun q hs => hs.filter (fun h => decide (¬ h.Equivalent q))) hs

theorem mem_residual (p : Formula s) (qs hs : List (Formula s)) :
    p ∈ residual qs hs ↔ p ∈ hs ∧ ∀ q ∈ qs, ¬ p.Equivalent q := by
  induction qs with
  | nil => simp [residual]
  | cons q qs ih =>
    simp only [residual, List.foldr_cons, List.mem_filter, decide_eq_true_eq]
    change (p ∈ residual qs hs ∧ ¬ p.Equivalent q) ↔ _
    rw [ih]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

theorem residual_self (hs : List (Formula s)) : residual hs hs = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro p hp
  obtain ⟨hp, hn⟩ := (mem_residual p hs hs).mp hp
  exact hn p hp rfl

theorem Derivable.dischargeList {t : Theory} {hs : List (Formula t.signature)}
    (qs : List (Formula t.signature)) {p : Formula t.signature} (d : Derivable t hs p) :
    Derivable t (residual qs hs) (implyList qs p) := by
  induction qs with
  | nil => exact d
  | cons q qs ih => exact .disch q ih

theorem Derivable.undischargeList {t : Theory} (qs : List (Formula t.signature))
    {hs : List (Formula t.signature)} {p : Formula t.signature}
    (d : Derivable t hs (implyList qs p)) : Derivable t (hs ++ qs) p := by
  induction qs generalizing hs with
  | nil => simpa only [List.append_nil] using d
  | cons q qs ih =>
    have dm := Derivable.mp d (Derivable.assume q)
    have di := ih dm
    simpa only [List.append_assoc, List.singleton_append] using di

theorem Substitution.apply_implyList (rs : Substitution s) (qs : List (Formula s))
    (p : Formula s) : rs.apply (implyList qs p) = implyList (qs.map rs.apply) (rs.apply p) := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    change rs.apply (.imp q (implyList qs p)) = .imp (rs.apply q) _
    rw [Substitution.apply_imp, ih]
    rfl

theorem Derivable.inst {t : Theory} {hs : List (Formula t.signature)}
    {p : Formula t.signature} (rs : Substitution t.signature) (d : Derivable t hs p) :
    Derivable t (hs.map rs.apply) (rs.apply p) := by
  have dd := d.dischargeList hs
  rw [residual_self] at dd
  have di := dd.instClosed rs
  rw [Substitution.apply_implyList] at di
  exact di.undischargeList _

end HotaruKernel
