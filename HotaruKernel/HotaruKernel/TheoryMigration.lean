import HotaruKernel.TheoryExtension
import HotaruKernel.RebaseSubstitution

namespace HotaruKernel

theorem Derivable.rebase {t u : Theory} (h : t.Extends u)
    {hs : List (Formula t.signature)} {p : Formula t.signature} (d : Derivable t hs p) :
    Derivable u (hs.map (Term.rebase h.signature)) (p.rebase h.signature) := by
  induction d with
  | context same d ih =>
    apply Derivable.context _ ih
    intro p
    constructor
    · intro hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact List.mem_map.mpr ⟨q, (same q).mp hq, rfl⟩
    · intro hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact List.mem_map.mpr ⟨q, (same q).mpr hq, rfl⟩
  | conversion he d ih =>
    apply Derivable.conversion _ ih
    simpa only [Term.Equivalent, Term.logical_rebase] using he
  | «axiom» p hp => exact .axiom _ (h.axioms p hp)
  | booleanAxiom hb =>
    cases hb with
    | impAntisym p q => exact .booleanAxiom (.impAntisym _ _)
  | assume p => exact .assume _
  | refl x => exact .refl _
  | beta hv b x =>
    have db := Derivable.beta (t := u) (h.signature.validType _ hv)
      (b.rebase h.signature) (x.rebase h.signature)
    simpa only [Term.rebase, Term.rebase_open] using db
  | holEquality a hv l r =>
    have dh := Derivable.holEquality (t := u) a (h.signature.validType _ hv)
      (l.rebase h.signature) (r.rebase h.signature)
    simpa only [Term.rebase, Term.holEquality] using dh
  | @abs b hs l r n a hv fresh d ih =>
    have df : ∀ p ∈ hs.map (Term.rebase h.signature), (n, a) ∉ p.freeVars := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      simpa only [Term.freeVars_rebase] using fresh q hq
    have da := Derivable.abs n a (h.signature.validType _ hv) df ih
    simpa only [Term.rebase, Term.rebase_abstract] using da
  | disch p d ih =>
    have dd := Derivable.disch (p.rebase h.signature) ih
    simpa only [Term.rebase, rebase_filter] using dd
  | mp di dp ihi ihp =>
    have dm := Derivable.mp ihi ihp
    simpa only [List.map_append] using dm
  | @instType hs p i hi d ih =>
    have di := Derivable.instType i (h.signature.validSubst i hi) ih
    have hm : hs.map (fun q => (q.instType i hi).rebase h.signature) =
        hs.map (fun q => (q.rebase h.signature).instType i (h.signature.validSubst i hi)) :=
      List.map_congr_left (fun q _ => q.rebase_instType h.signature i hi)
    have hc := p.rebase_instType h.signature i hi
    simp only [List.map_map, Function.comp_def] at di ⊢
    exact Eq.mpr (congrArg₂ (Derivable u) hm hc) di
  | @subst hs rs template eqs d iheqs ih =>
    let entries := rs.map (fun r => r.rebase h.signature)
    have he : ∀ r ∈ entries, Derivable u r.hypotheses (.equal r.left r.right) := by
      intro r hr
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
      exact iheqs q hq
    have ih' : Derivable u (hs.map (Term.rebase h.signature))
        ((rewriteSubst entries false).apply (template.rebase h.signature)) := by
      simpa only [Substitution.apply_rebase, rewriteSubst_rebase] using ih
    have ds := Derivable.subst entries (template.rebase h.signature) he ih'
    simpa only [List.map_append, rewriteHypotheses_rebase,
      Substitution.apply_rebase, rewriteSubst_rebase] using ds

def Thm.rebase {t u : Theory} (h : t.Extends u) (th : Thm t) : Thm u :=
  ⟨th.assumptions.map (Term.rebase h.signature), th.conclusion.rebase h.signature,
    th.derivation.rebase h, (th.origin.join t.origin).join u.origin⟩

def Kernel.MIGRATE {t : Theory} (e : TheoryExtension t) (th : Thm t) :
    Except KernelError (Thm e.target) := .ok (th.rebase e.extension)

theorem Thm.rebase_sound {t u : Theory} (h : t.Extends u) (th : Thm t) :
    u.Entails (th.assumptions.map (Term.rebase h.signature))
      (th.conclusion.rebase h.signature) := (th.rebase h).sound

end HotaruKernel
