import HotaruKernel.Kernel
import HotaruKernel.ExtensionSemantics

namespace HotaruKernel

structure Theory.Extends (t u : Theory) : Prop where
  signature : t.signature.Extends u.signature
  axioms : ∀ p ∈ t.axioms, p.rebase signature ∈ u.axioms

theorem Theory.Extends.refl (t : Theory) : t.Extends t where
  signature := .refl _
  axioms p hp := by simpa only [Term.rebase_refl] using hp

theorem Theory.Extends.trans {t u v : Theory} (h : t.Extends u) (k : u.Extends v) :
    t.Extends v where
  signature := h.signature.trans k.signature
  axioms p hp := by
    have hx := k.axioms _ (h.axioms p hp)
    simpa only [Term.rebase_trans] using hx

theorem Theory.Extends.models {t u : Theory} (h : t.Extends u)
    (p : PolymorphicModel u.signature) (hp : Models u p) :
    Models t (p.restrict h.signature) := by
  intro m hm f q hq
  exact (Formula.eval_rebase_polymorphic q h.signature p m hm f).symm.trans
    (hp m hm f _ (h.axioms q hq))

theorem Theory.Extends.entails {t u : Theory} (h : t.Extends u)
    {hs : List (Formula t.signature)} {q : Formula t.signature} (d : t.Entails hs q) :
    u.Entails (hs.map (Term.rebase h.signature)) (q.rebase h.signature) := by
  intro p hp m hm f hh
  apply (Formula.eval_rebase_polymorphic q h.signature p m hm f).trans
  apply d (p.restrict h.signature) (h.models p hp) m hm f
  intro a ha
  exact (Formula.eval_rebase_polymorphic a h.signature p m hm f).symm.trans
    (hh _ (List.mem_map.mpr ⟨a, ha, rfl⟩))

def Theory.withSignature (t : Theory) (s : Signature) (h : t.signature.Extends s) : Theory :=
  ⟨s, t.axioms.map (Term.rebase h), t.origin⟩

theorem Theory.extends_withSignature (t : Theory) (s : Signature)
    (h : t.signature.Extends s) : t.Extends (t.withSignature s h) where
  signature := h
  axioms p hp := List.mem_map.mpr ⟨p, hp, rfl⟩

theorem Theory.models_withSignature_iff (t : Theory) (s : Signature)
    (h : t.signature.Extends s) (p : PolymorphicModel s) :
    Models (t.withSignature s h) p ↔ Models t (p.restrict h) := by
  constructor
  · exact (t.extends_withSignature s h).models p
  · intro hp m hm f q hq
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
    exact (Formula.eval_rebase_polymorphic a h p m hm f).trans (hp m hm f a ha)

structure TheoryExtension (t : Theory) where
  target : Theory
  extension : t.Extends target
  wellFormed : target.signature.WellFormed

namespace Kernel

def MARK_THEORY (t : Theory) (source : Provenance.Source) :
    Except KernelError (TheoryExtension t) :=
  if hw : t.signature.WellFormed then
    .ok ⟨{ t with origin := t.origin.join (.source source) },
      ⟨.refl _, fun _ hp => by simpa only [Term.rebase_refl] using hp⟩, hw⟩
  else .error .invalidSignature

def DECLARE_TYPE (t : Theory) (n : QName) (arity : Nat) :
    Except KernelError (TheoryExtension t) := do
  if hw : t.signature.WellFormed then
    if hn : t.signature.typeOps.lookup n = none then
      let h := t.signature.extends_addType n arity hn
      return ⟨t.withSignature _ h, t.extends_withSignature _ h, hw.addType n arity hn⟩
    else .error .duplicateType
  else .error .invalidSignature

def DECLARE_CONSTANT (t : Theory) (n : QName) (scheme : HolType) :
    Except KernelError (TheoryExtension t) := do
  if hw : t.signature.WellFormed then
    if hn : t.signature.constants.lookup n = none then
      if hv : t.signature.validType scheme = true then
        let h := t.signature.extends_addConstant n scheme hn
        return ⟨t.withSignature _ h, t.extends_withSignature _ h,
          hw.addConstant n scheme hn hv⟩
      else .error .invalidType
    else .error .duplicateConstant
  else .error .invalidSignature

theorem extension_success {t : Theory} (result : Except KernelError (TheoryExtension t))
    (e : TheoryExtension t) (_h : result = .ok e) :
    t.Extends e.target ∧ e.target.signature.WellFormed := ⟨e.extension, e.wellFormed⟩

end Kernel
end HotaruKernel
