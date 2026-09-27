import HotaruKernel.Check
import HotaruKernel.InstDerivation

namespace HotaruKernel

structure CheckedTerm (t : Theory) where
  type : HolType
  term : Closed t.signature type

def checkClosed (t : Theory) (r : RawTerm) : Except KernelError (CheckedTerm t) := do
  let p ← check t.signature [] r
  return ⟨p.type, p.term⟩

structure Thm (t : Theory) where
  assumptions : List (Formula t.signature)
  conclusion : Formula t.signature
  derivation : Derivable t assumptions conclusion
  origin : Provenance.Origin

def Thm.mark (th : Thm t) (source : Provenance.Source) : Thm t :=
  { th with origin := (th.origin.join t.origin).join (.source source) }

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

structure ImplicationView (p : Formula s) where
  antecedent : Formula s
  consequent : Formula s
  equation : p = .imp antecedent consequent

def implicationView : (p : Formula s) → Except KernelError (ImplicationView p)
  | .imp p q => .ok ⟨p, q, rfl⟩
  | _ => .error .notImplication

namespace Kernel

def INST_TYPE (t : Theory) (i : TypeSubst) (th : Thm t) : Except KernelError (Thm t) :=
  if hi : i.Valid t.signature then
    .ok ⟨th.assumptions.map (Term.instType i hi), th.conclusion.instType i hi,
      .instType i hi th.derivation, t.origin.join th.origin⟩
  else .error .invalidType

def ASSUME_CHECKED (t : Theory) (p : CheckedTerm t) : Except KernelError (Thm t) := do
  if h : p.type = .bool then
    let q : Term t.signature [] .bool := h ▸ p.term
    return ⟨[q], q, .assume q, t.origin⟩
  else .error .notBoolean

def ASSUME (t : Theory) (p : RawTerm) : Except KernelError (Thm t) := do
  ASSUME_CHECKED t (← checkClosed t p)

def REFL_CHECKED (t : Theory) (p : CheckedTerm t) : Thm t :=
  ⟨[], .equal p.term p.term, .refl p.term, t.origin⟩

def REFL (t : Theory) (r : RawTerm) : Except KernelError (Thm t) := do
  return REFL_CHECKED t (← checkClosed t r)

def betaChecked (t : Theory) : Closed t.signature a → Except KernelError (Thm t)
  | .app (.lam valid b) x =>
      .ok ⟨[], .equal (.app (.lam valid b) x) (b.open x), .beta valid b x, t.origin⟩
  | _ => .error .notBetaRedex

def BETA_CONV_CHECKED (t : Theory) (p : CheckedTerm t) : Except KernelError (Thm t) :=
  betaChecked t p.term

def BETA_CONV (t : Theory) (r : RawTerm) : Except KernelError (Thm t) := do
  BETA_CONV_CHECKED t (← checkClosed t r)

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
        .abs n a valid fresh d, (t.origin.join th.origin)⟩
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
          .equal (.app f (h ▸ x)) (.app g (h ▸ y)), .mkComb df dx,
          (t.origin.join tf.origin).join tx.origin⟩
      else .error .typeMismatch
  | _ => .error .notFunction

def DISCH_CHECKED (t : Theory) (p : CheckedTerm t) (th : Thm t) :
    Except KernelError (Thm t) := do
  let ⟨a, p'⟩ := p
  if h : a = .bool then
    let q : Term t.signature [] .bool := h ▸ p'
    return ⟨th.assumptions.filter (fun p => decide (¬ p.Equivalent q)), .imp q th.conclusion,
      .disch q th.derivation, t.origin.join th.origin⟩
  else .error .notBoolean

def DISCH (t : Theory) (p : RawTerm) (th : Thm t) : Except KernelError (Thm t) := do
  DISCH_CHECKED t (← checkClosed t p) th

def MP (t : Theory) (ti tp : Thm t) : Except KernelError (Thm t) := do
  let e ← implicationView ti.conclusion
  if h : e.antecedent.Equivalent tp.conclusion then
    have di : Derivable t ti.assumptions (.imp e.antecedent e.consequent) := by
      rw [← e.equation]; exact ti.derivation
    have dp : Derivable t tp.assumptions e.antecedent := .conversion h.symm tp.derivation
    return ⟨ti.assumptions ++ tp.assumptions, e.consequent, .mp di dp,
      (t.origin.join ti.origin).join tp.origin⟩
  else .error .termMismatch

def SYM (t : Theory) (th : Thm t) : Except KernelError (Thm t) := do
  let e ← equationView th.conclusion
  have d : Derivable t th.assumptions (.equal e.left e.right) := by
    rw [← e.equation]; exact th.derivation
  return ⟨th.assumptions, .equal e.right e.left, .symm d, t.origin.join th.origin⟩

def TRANS (t : Theory) (tl tr : Thm t) : Except KernelError (Thm t) := do
  let ⟨a, l, r, hl⟩ ← equationView tl.conclusion
  let ⟨b, r', u, hr⟩ ← equationView tr.conclusion
  if ht : b = a then
    let middle : Term t.signature [] a := ht ▸ r'
    let last : Term t.signature [] a := ht ▸ u
    if hm : r.Equivalent middle then
      have dl : Derivable t tl.assumptions (.equal l r) := by
        rw [← hl]; exact tl.derivation
      have dr : Derivable t tr.assumptions (.equal r last) := by
        apply Derivable.conversion (p := .equal middle last) (q := .equal r last)
          (congrArg (fun x => LogicalTerm.equal x last.logical) hm.symm)
        subst b
        rw [← hr]; exact tr.derivation
      return ⟨tl.assumptions ++ tr.assumptions, .equal l last, .trans dl dr,
        (t.origin.join tl.origin).join tr.origin⟩
    else .error .termMismatch
  else .error .typeMismatch

def EQ_MP (t : Theory) (te tp : Thm t) : Except KernelError (Thm t) := do
  let ⟨a, p, q, he⟩ ← equationView te.conclusion
  if ht : a = .bool then
    let antecedent : Term t.signature [] .bool := ht ▸ p
    let consequent : Term t.signature [] .bool := ht ▸ q
    if hp : antecedent.Equivalent tp.conclusion then
      have de : Derivable t te.assumptions (.equal antecedent consequent) := by
        subst a
        rw [← he]; exact te.derivation
      have dp : Derivable t tp.assumptions antecedent := .conversion hp.symm tp.derivation
      return ⟨te.assumptions ++ tp.assumptions, consequent, .eqMp de dp,
        (t.origin.join te.origin).join tp.origin⟩
    else .error .termMismatch
  else .error .notBoolean

def checkReplacement (s : Signature) (target value : RawTerm) :
    Except KernelError (Replacement s) := do
  match target with
  | .fvar n a =>
      if s.validType a then
        let ⟨b, term, _⟩ ← check s [] value
        if h : b = a then return ⟨a, n, h ▸ term⟩
        else .error .typeMismatch
      else .error .invalidType
  | _ => .error .notVariable

def INST (t : Theory) (rs : List (RawTerm × RawTerm)) (th : Thm t) :
    Except KernelError (Thm t) := do
  let subst ← rs.mapM (fun (v, r) => checkReplacement t.signature v r)
  return ⟨th.assumptions.map (Substitution.apply subst),
    Substitution.apply subst th.conclusion, .inst subst th.derivation, t.origin.join th.origin⟩

structure CertifiedRewrite (t : Theory) where
  entry : RewriteEntry t.signature
  derivation : Derivable t entry.hypotheses (.equal entry.left entry.right)

def checkRewrite (t : Theory) (target : RawTerm) (th : Thm t) :
    Except KernelError (CertifiedRewrite t) := do
  match target with
  | .fvar n a =>
      let ⟨b, l, r, he⟩ ← equationView th.conclusion
      if ht : b = a then
        have d : Derivable t th.assumptions (.equal (ht ▸ l) (ht ▸ r)) := by
          subst b
          rw [← he]; exact th.derivation
        return ⟨⟨a, n, ht ▸ l, ht ▸ r, th.assumptions⟩, d⟩
      else .error .typeMismatch
  | _ => .error .notVariable

def SUBST (t : Theory) (rs : List (RawTerm × Thm t)) (template : RawTerm) (th : Thm t) :
    Except KernelError (Thm t) := do
  let entries ← rs.mapM (fun (v, e) => checkRewrite t v e)
  let rules := entries.map CertifiedRewrite.entry
  have eqs : ∀ r ∈ rules, Derivable t r.hypotheses (.equal r.left r.right) := by
    intro r hr
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hr
    exact e.derivation
  let ⟨a, p, _⟩ ← check t.signature [] template
  if ha : a = .bool then
    let body : Term t.signature [] .bool := ha ▸ p
    let left := (rewriteSubst rules false).apply body
    if hc : left.Equivalent th.conclusion then
      have d : Derivable t th.assumptions left := .conversion hc.symm th.derivation
      return ⟨rewriteHypotheses rules ++ th.assumptions,
        (rewriteSubst rules true).apply body, .subst rules body eqs d,
        t.origin.collect (th.origin :: rs.map (fun r => r.2.origin))⟩
    else .error .termMismatch
  else .error .notBoolean

-- This theorem applies uniformly to every successful public kernel call.
theorem success_sound (result : Except KernelError (Thm t)) (th : Thm t)
    (_h : result = .ok th) : t.Entails th.assumptions th.conclusion := th.sound

end Kernel
end HotaruKernel
