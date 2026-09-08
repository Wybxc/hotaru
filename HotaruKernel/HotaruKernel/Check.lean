import HotaruKernel.Syntax

namespace HotaruKernel

variable {ctx dst : List HolType}

inductive KernelError where
  | invalidType
  | unboundVariable
  | unknownConstant
  | notFunction
  | typeMismatch
  | notBoolean
  | notEquation
  | notBetaRedex
  | freeInAssumptions
  deriving DecidableEq, Repr

structure Checked (s : Signature) (ctx : List HolType) (r : RawTerm) where
  type : HolType
  term : Term s ctx type
  erases : term.raw = r

def checkVar : (ctx : List HolType) → (n : Nat) →
    Except KernelError (Σ a, {v : BVar ctx a // v.index = n})
  | [], _ => .error .unboundVariable
  | a :: _, 0 => .ok ⟨a, .zero, rfl⟩
  | _ :: ctx, n + 1 => do
      let ⟨a, v, h⟩ ← checkVar ctx n
      return ⟨a, .succ v, congrArg (· + 1) h⟩

def check (s : Signature) (ctx : List HolType) :
    (r : RawTerm) → Except KernelError (Checked s ctx r)
  | .fvar n a =>
      if h : s.validType a = true then .ok ⟨a, .fvar n a h, rfl⟩
      else .error .invalidType
  | .bvar n => do
      let ⟨a, v, h⟩ ← checkVar ctx n
      return ⟨a, .bvar v, by simp [Term.raw, h]⟩
  | .const n i =>
      match h : s.constants.lookup n with
      | none => .error .unknownConstant
      | some scheme =>
          if hv : s.validType (scheme.inst i) = true then
            .ok ⟨scheme.inst i, .const n scheme i h hv, rfl⟩
          else .error .invalidType
  | .app g x => do
      let ⟨gt, g', hg⟩ ← check s ctx g
      let ⟨xt, x', hx⟩ ← check s ctx x
      match gt with
      | .fn a b =>
          if h : xt = a then
            return ⟨b, .app g' (h ▸ x'), by subst xt; simp [Term.raw, hg, hx]⟩
          else .error .typeMismatch
      | _ => .error .notFunction
  | .lam a b =>
      if h : s.validType a = true then do
        let ⟨bt, b', hb⟩ ← check s (a :: ctx) b
        return ⟨.fn a bt, .lam h b', by simp [Term.raw, hb]⟩
      else .error .invalidType
  | .equal l r => do
      let ⟨lt, l', hl⟩ ← check s ctx l
      let ⟨rt, r', hr⟩ ← check s ctx r
      if h : rt = lt then
        return ⟨.bool, .equal l' (h ▸ r'), by subst rt; simp [Term.raw, hl, hr]⟩
      else .error .typeMismatch

-- An extrinsic typing judgment makes the checker specification independent
-- of both the checking algorithm and the theorem inference system.
inductive HasType (s : Signature) : List HolType → RawTerm → HolType → Prop where
  | fvar {ctx : List HolType} (h : s.validType a = true) : HasType s ctx (.fvar n a) a
  | bvar {ctx : List HolType} (v : BVar ctx a) : HasType s ctx (.bvar v.index) a
  | const {ctx : List HolType} {scheme : HolType} (h : s.constants.lookup n = some scheme)
      (hv : s.validType (scheme.inst i) = true) :
      HasType s ctx (.const n i) (scheme.inst i)
  | app {ctx : List HolType} : HasType s ctx f (.fn a b) → HasType s ctx x a →
      HasType s ctx (.app f x) b
  | lam {ctx : List HolType} : s.validType a = true → HasType s (a :: ctx) b t →
      HasType s ctx (.lam a b) (.fn a t)
  | equal {ctx : List HolType} : HasType s ctx l a → HasType s ctx r a →
      HasType s ctx (.equal l r) .bool

theorem Term.hasType (t : Term s ctx a) : HasType s ctx t.raw a := by
  induction t with
  | fvar n a h => exact .fvar h
  | bvar v => exact .bvar v
  | const n t i h hv => exact .const h hv
  | app _ _ hf hx => exact .app hf hx
  | lam h _ hb => exact .lam h hb
  | equal _ _ hl hr => exact .equal hl hr

theorem BVar.validType {s : Signature} (v : BVar ctx a)
    (h : ∀ b ∈ ctx, s.validType b = true) :
    s.validType a = true := by
  induction v with
  | zero => exact h _ (by simp)
  | succ v ih => exact ih (fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem Term.validType (t : Term s ctx a) (h : ∀ b ∈ ctx, s.validType b = true) :
    s.validType a = true := by
  induction t with
  | fvar _ _ hv => exact hv
  | bvar v => exact v.validType h
  | const _ _ _ _ hv => exact hv
  | app _ _ hf _ =>
    have hv := hf h
    simp only [Signature.validType, Bool.and_eq_true] at hv
    exact hv.2
  | lam hv _ ih =>
    simp only [Signature.validType, Bool.and_eq_true]
    refine ⟨hv, ih ?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hv
    · exact h b hb
  | equal => simp [Signature.validType]

theorem check_sound (s : Signature) (ctx : List HolType) (r : RawTerm)
    (c : Checked s ctx r) (_h : check s ctx r = .ok c) : HasType s ctx r c.type := by
  have h := c.term.hasType
  rw [c.erases] at h
  exact h

theorem substBound_preserves_type (t : Term s ctx a) (r : BoundSubst s ctx dst) :
    HasType s dst (t.substBound r).raw a := (t.substBound r).hasType

theorem substFree_preserves_type (t : Term s ctx a) (r : FreeSubst s dst)
    (q : Renaming ctx dst) : HasType s dst (t.substFree r q).raw a :=
  (t.substFree r q).hasType

end HotaruKernel
