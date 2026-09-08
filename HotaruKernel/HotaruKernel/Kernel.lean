import HotaruKernel.Check
import HotaruKernel.Inference

namespace HotaruKernel

structure Thm (t : Theory) where
  assumptions : List (Formula t.signature)
  conclusion : Formula t.signature
  derivation : Derivable t assumptions conclusion

theorem Thm.sound (h : Thm t) : t.Entails h.assumptions h.conclusion :=
  h.derivation.sound

structure EquationView (p : Formula s) where
  type : HolType
  left : Closed s type
  right : Closed s type
  equation : p = .equal left right

def equationView : (p : Formula s) → Except KernelError (EquationView p)
  | .equal l r => .ok ⟨_, l, r, rfl⟩
  | _ => .error .notEquation

namespace Kernel

def ASSUME (t : Theory) (p : RawTerm) : Except KernelError (Thm t) := do
  let ⟨a, p', _⟩ ← check t.signature [] p
  if h : a = .bool then
    let q : Term t.signature [] .bool := h ▸ p'
    return ⟨[q], q, .assume q⟩
  else .error .notBoolean

def REFL (t : Theory) (r : RawTerm) : Except KernelError (Thm t) := do
  let p ← check t.signature [] r
  return ⟨[], .equal p.term p.term, .refl p.term⟩

def betaChecked (t : Theory) : Closed t.signature a → Except KernelError (Thm t)
  | .app (.lam valid b) x =>
      .ok ⟨[], .equal (.app (.lam valid b) x) (b.open x), .beta valid b x⟩
  | _ => .error .notBetaRedex

def BETA_CONV (t : Theory) (r : RawTerm) : Except KernelError (Thm t) := do
  let p ← check t.signature [] r
  betaChecked t p.term

def ABS (t : Theory) (n : String) (a : HolType) (th : Thm t) :
    Except KernelError (Thm t) := do
  if valid : t.signature.validType a = true then
    let e ← equationView th.conclusion
    if fresh : ∀ p ∈ th.assumptions, (n, a) ∉ p.freeVars then
      have d : Derivable t th.assumptions (.equal e.left e.right) := by
        rw [← e.equation]
        exact th.derivation
      return ⟨th.assumptions,
        .equal (e.left.abstract n a valid) (e.right.abstract n a valid),
        .abs n a valid fresh d⟩
    else .error .freeInAssumptions
  else .error .invalidType

def MK_COMB (t : Theory) (tf tx : Thm t) : Except KernelError (Thm t) := do
  let ⟨ft, f, g, hf⟩ ← equationView tf.conclusion
  let ⟨xt, x, y, hx⟩ ← equationView tx.conclusion
  match ft with
  | .fn a b =>
      if h : xt = a then
        have df : Derivable t tf.assumptions (.equal f g) := by
          rw [← hf]; exact tf.derivation
        have dx : Derivable t tx.assumptions (.equal (h ▸ x) (h ▸ y)) := by
          subst xt
          rw [← hx]; exact tx.derivation
        return ⟨tf.assumptions ++ tx.assumptions,
          .equal (.app f (h ▸ x)) (.app g (h ▸ y)), .mkComb df dx⟩
      else .error .typeMismatch
  | _ => .error .notFunction

-- This theorem applies uniformly to every successful public kernel call.
theorem success_sound (result : Except KernelError (Thm t)) (th : Thm t)
    (_h : result = .ok th) : t.Entails th.assumptions th.conclusion := th.sound

end Kernel
end HotaruKernel
