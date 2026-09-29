import HotaruKernel.TypeDefinition

/-! Source propagation for the core kernel operations themselves. -/
namespace HotaruKernel
open Provenance

variable {t : Theory} {src : Source}

theorem Theory.complete (t : Theory) :
    Depends t.origin.history src → src ∈ t.origin.sources := t.origin.complete

theorem ConstantDefinition.target_origin (d : ConstantDefinition t) :
    d.target.origin = t.origin := rfl

theorem ConstantDefinition.definition_origin (d : ConstantDefinition t) :
    d.definitionThm.origin = d.target.origin := rfl

theorem TypeDefinition.definition_origin (d : TypeDefinition t) :
    d.definitionThm.origin = d.target.origin := rfl

theorem Thm.complete (th : Thm t) :
    Depends th.origin.history src → src ∈ th.origin.sources := th.origin.complete

theorem Thm.kind_absent (th : Thm t) (kind : Kind)
    (h : ∀ s ∈ th.origin.sources, s.kind ≠ kind) :
    ∀ s, s.kind = kind → ¬ Depends th.origin.history s := th.origin.kind_absent kind h

theorem Thm.mark_sources (th : Thm t) (source : Source) :
    src ∈ (th.mark source).origin.sources ↔
      (src ∈ th.origin.sources ∨ src ∈ t.origin.sources) ∨ src = source := by
  simp [mark, Origin.source]

theorem Thm.rebase_sources {u : Theory} (h : t.Extends u) (th : Thm t) :
    src ∈ (th.rebase h).origin.sources ↔
      (src ∈ th.origin.sources ∨ src ∈ t.origin.sources) ∨ src ∈ u.origin.sources := by
  simp [rebase]

namespace Kernel

-- Split executable checks, then use the successful constructor's origin field.
macro "source_check" h:ident : tactic =>
  `(tactic| (repeat' first
    | split at $h:ident
    | (simp only [bind, Except.bind, pure, Except.pure] at $h:ident; split at $h:ident)
    | cases $h:ident
    | rfl))

theorem assume_origin (p : RawTerm) (out : Thm t) (h : ASSUME t p = .ok out) :
    out.origin = t.origin := by
  unfold ASSUME at h
  cases hc : checkClosed t p with
  | error e => simp [hc, bind, Except.bind] at h
  | ok checked =>
    have h' : ASSUME_CHECKED t checked = .ok out := by simpa [hc] using h
    unfold ASSUME_CHECKED at h'
    source_check h'

theorem refl_origin (p : RawTerm) (out : Thm t) (h : REFL t p = .ok out) :
    out.origin = t.origin := by
  unfold REFL at h
  source_check h

theorem betaChecked_origin (p : Closed t.signature a) (out : Thm t)
    (h : betaChecked t p = .ok out) : out.origin = t.origin := by
  unfold betaChecked at h
  source_check h

theorem beta_origin (p : RawTerm) (out : Thm t) (h : BETA_CONV t p = .ok out) :
    out.origin = t.origin := by
  unfold BETA_CONV at h
  cases hc : checkClosed t p with
  | error e => simp [hc, bind, Except.bind] at h
  | ok checked =>
    exact betaChecked_origin checked.term out (by simpa [hc, BETA_CONV_CHECKED] using h)

theorem instType_origin (i : TypeSubst) (th out : Thm t)
    (h : INST_TYPE t i th = .ok out) : out.origin = t.origin.join th.origin := by
  unfold INST_TYPE at h
  source_check h

theorem abs_origin (n : String) (a : HolType) (th out : Thm t)
    (h : ABS t n a th = .ok out) : out.origin = t.origin.join th.origin := by
  unfold ABS at h
  source_check h

theorem mkComb_origin (l r out : Thm t) (h : MK_COMB t l r = .ok out) :
    out.origin = (t.origin.join l.origin).join r.origin := by
  unfold MK_COMB at h
  source_check h

theorem disch_origin (p : RawTerm) (th out : Thm t) (h : DISCH t p th = .ok out) :
    out.origin = t.origin.join th.origin := by
  unfold DISCH at h
  cases hc : checkClosed t p with
  | error e => simp [hc, bind, Except.bind] at h
  | ok checked =>
    have h' : DISCH_CHECKED t checked th = .ok out := by simpa [hc] using h
    unfold DISCH_CHECKED at h'
    source_check h'

theorem mp_origin (l r out : Thm t) (h : MP t l r = .ok out) :
    out.origin = (t.origin.join l.origin).join r.origin := by
  unfold MP at h
  source_check h

theorem sym_origin (th out : Thm t) (h : SYM t th = .ok out) :
    out.origin = t.origin.join th.origin := by
  unfold SYM at h
  source_check h

theorem trans_origin (l r out : Thm t) (h : TRANS t l r = .ok out) :
    out.origin = (t.origin.join l.origin).join r.origin := by
  unfold TRANS at h
  source_check h

set_option maxHeartbeats 1000000 in
-- The fused equality checker has dependent branches whose source proof needs a larger budget.
theorem eqMp_origin (l r out : Thm t) (h : EQ_MP t l r = .ok out) :
    out.origin = (t.origin.join l.origin).join r.origin := by
  unfold EQ_MP at h
  cases hm : eqMpRaw t l r with
  | error e => simp [Except.map, hm] at h
  | ok value =>
      simp only [Except.map, hm] at h
      cases h
      exact value.property

theorem inst_origin (rs : List (RawTerm × RawTerm)) (th out : Thm t)
    (h : INST t rs th = .ok out) : out.origin = t.origin.join th.origin := by
  unfold INST at h
  source_check h

theorem subst_origin (rs : List (RawTerm × Thm t)) (p : RawTerm) (th out : Thm t)
    (h : SUBST t rs p th = .ok out) :
    out.origin = t.origin.collect (th.origin :: rs.map (fun r => r.2.origin)) := by
  unfold SUBST at h
  source_check h

theorem declareType_origin (name : QName) (arity : Nat) (e : TheoryExtension t)
    (h : DECLARE_TYPE t name arity = .ok e) : e.target.origin = t.origin := by
  unfold DECLARE_TYPE DECLARE_TYPE_VALID at h
  source_check h

theorem declareConstant_origin (name : QName) (ty : HolType) (e : TheoryExtension t)
    (h : DECLARE_CONSTANT t name ty = .ok e) : e.target.origin = t.origin := by
  unfold DECLARE_CONSTANT DECLARE_CONSTANT_VALID at h
  source_check h

theorem markTheory_origin (source : Source) (e : TheoryExtension t)
    (h : MARK_THEORY t source = .ok e) :
    e.target.origin = t.origin.join (.source source) := by
  unfold MARK_THEORY at h
  source_check h

theorem defineType_origin (name : QName) (params : List String) (p : RawTerm)
    (proof : Option (Thm t)) (d : TypeDefinition t)
    (h : DEFINE_TYPE t name params p proof = .ok d) :
    ∃ th, proof = some th ∧ d.proofOrigin = th.origin := by
  unfold DEFINE_TYPE at h
  source_check h
  exact ⟨_, rfl, rfl⟩

theorem subst_sources (rs : List (RawTerm × Thm t)) (p : RawTerm) (th out : Thm t)
    (h : SUBST t rs p th = .ok out) :
    src ∈ out.origin.sources ↔ src ∈ t.origin.sources ∨ src ∈ th.origin.sources ∨
      ∃ entry ∈ rs, src ∈ entry.2.origin.sources := by
  rw [subst_origin rs p th out h, Origin.mem_collect]
  simp

theorem defineType_sources (name : QName) (params : List String) (p : RawTerm)
    (proof : Thm t) (d : TypeDefinition t)
    (h : DEFINE_TYPE t name params p (some proof) = .ok d) :
    src ∈ d.target.origin.sources ↔ src ∈ t.origin.sources ∨ src ∈ proof.origin.sources := by
  obtain ⟨th, he, ho⟩ := defineType_origin name params p (some proof) d h
  cases he
  simp [TypeDefinition.target, ho]

end Kernel
end HotaruKernel
