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

private def unionAssumptions {t : Theory} (a b : List (Formula t.signature)) :
    List (Formula t.signature) :=
  match a, b with
  | [], bs => bs
  | as, [] => as
  | as, bs => (as ++ bs).eraseDups

private theorem mem_unionAssumptions {t : Theory} {a b : List (Formula t.signature)}
    {x : Formula t.signature} :
    x ∈ a ∨ x ∈ b ↔ x ∈ unionAssumptions a b := by
  cases a <;> cases b <;>
    simp [unionAssumptions, List.mem_eraseDups, or_comm, or_assoc, or_left_comm]

private theorem mem_unionAssumptions_swap {t : Theory} {a b : List (Formula t.signature)}
    {x : Formula t.signature} :
    x ∈ b ∨ x ∈ a ↔ x ∈ unionAssumptions a b := by
  cases a <;> cases b <;>
    simp [unionAssumptions, List.mem_eraseDups, or_comm, or_assoc, or_left_comm]

def CONTRACT (t : Theory) (th : Thm t) : Thm t :=
  if th.assumptions.length ≤ 1 then th else
    ⟨th.assumptions.eraseDups, th.conclusion,
      .context (fun _ => by simp) th.derivation, th.origin⟩

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

private def holEqualityTerm {t : Theory} (a : HolType)
    (ha : t.signature.validType a = true) (l r : Closed t.signature a) : Closed t.signature .bool :=
  let body : Term t.signature [a] (.fn a .bool) :=
    .lam ha (.equal (.bvar (.succ .zero)) (.bvar .zero))
  let connective : Closed t.signature (.fn a (.fn a .bool)) := .lam ha body
  .app (.app connective l) r

private def holEqualityBridge {t : Theory} (a : HolType)
    (ha : t.signature.validType a = true) (l r : Closed t.signature a) : Thm t :=
  let body : Term t.signature [a] (.fn a .bool) :=
    .lam ha (.equal (.bvar (.succ .zero)) (.bvar .zero))
  let connective : Closed t.signature (.fn a (.fn a .bool)) := .lam ha body
  let firstRedex : Closed t.signature (.fn a .bool) := .app connective l
  let secondBody : Term t.signature [a] .bool :=
    .equal l.weaken (.bvar .zero)
  let secondLambda : Closed t.signature (.fn a .bool) := .lam ha secondBody
  let first : Thm t :=
    ⟨[], .equal firstRedex (body.open l), .beta ha body l, t.origin⟩
  let rightRefl : Thm t := ⟨[], .equal r r, .refl r, t.origin⟩
  let applied : Thm t :=
    ⟨[], .equal (.app firstRedex r) (.app secondLambda r),
      .mkComb first.derivation rightRefl.derivation,
      (t.origin.join first.origin).join rightRefl.origin⟩
  let secondRedex : Closed t.signature .bool := .app secondLambda r
  let secondDerivation : Derivable t [] (.equal secondRedex (.equal l r)) := by
    have beta : Derivable t [] (.equal secondRedex (secondBody.open r)) :=
      .beta ha secondBody r
    apply Derivable.conversion (p := .equal secondRedex (secondBody.open r))
    · have hbody : secondBody.open r = .equal l r := by
        change Term.equal ((l.weaken).open r) r = Term.equal l r
        rw [Term.weaken_open]
      exact congrArg
        (fun x : Term t.signature [] .bool => (Term.equal secondRedex x).logical) hbody
    · exact beta
  let second : Thm t :=
    ⟨[], .equal secondRedex (.equal l r), secondDerivation, t.origin⟩
  ⟨[], .equal (.app firstRedex r) (.equal l r),
    .trans applied.derivation second.derivation,
    (t.origin.join applied.origin).join second.origin⟩

def normalizeHolEquality (t : Theory) (th : Thm t) : Except KernelError (Thm t) := do
  match he : th.conclusion with
  | .app (.app (.lam ha (.lam _ (.equal (.bvar (.succ .zero)) (.bvar .zero)))) l) r =>
      let bridge := holEqualityBridge _ ha l r
      have d : Derivable t th.assumptions _ := by
        rw [← he]
        exact th.derivation
      return ⟨th.assumptions, .equal l r, .eqMp bridge.derivation d,
        th.origin⟩
  | _ => .ok th

def expandHolEquality (t : Theory) (th : Thm t) : Except KernelError (Thm t) := do
  match he : th.conclusion with
  | .equal l r =>
      let ha := l.validType (fun _ h => by cases h)
      let bridge := holEqualityBridge _ ha l r
      let article := holEqualityTerm _ ha l r
      have d : Derivable t th.assumptions (.equal l r) := by
        rw [← he]
        exact th.derivation
      have derivation : Derivable t th.assumptions article := by
        simpa only [article, bridge, holEqualityTerm, holEqualityBridge, List.nil_append] using
          .eqMp (.symm bridge.derivation) d
      return ⟨th.assumptions, article, derivation, th.origin⟩
  | _ => .ok th

def isNativeEquality {t : Theory} {a : HolType} (p : Term t.signature [] a) : Bool :=
  match p with
  | .equal _ _ => true
  | _ => false

def isHolEquality {t : Theory} {a : HolType} (p : Term t.signature [] a) : Bool :=
  match p with
  | .app (.app (.lam _ (.lam _ (.equal (.bvar (.succ .zero)) (.bvar .zero)))) _) _ => true
  | _ => false

def alignHolEqualityPremise (t : Theory) (antecedent : Term t.signature [] .bool) (th : Thm t) :
    Except KernelError (Thm t) :=
  if isNativeEquality antecedent then
    normalizeHolEquality t th
  else if isHolEquality antecedent then
    expandHolEquality t th
  else
    .ok th

def ABS (t : Theory) (n : String) (a : HolType) (th : Thm t) :
    Except KernelError (Thm t) := do
  let thOrigin := th.origin
  let th ← normalizeHolEquality t th
  if valid : t.signature.validType a = true then
    let e ← equationView th.conclusion
    if fresh : ∀ p ∈ th.assumptions, (n, a) ∉ p.freeVars then
      have d : Derivable t th.assumptions (.equal e.left e.right) := by
        rw [← e.equation]
        exact th.derivation
      return ⟨th.assumptions,
        .equal (e.left.abstract n a valid) (e.right.abstract n a valid),
        .abs n a valid fresh d, (t.origin.join thOrigin)⟩
    else .error .freeInAssumptions
  else .error .invalidType

def MK_COMB (t : Theory) (tf tx : Thm t) : Except KernelError (Thm t) := do
  let tfOrigin := tf.origin
  let txOrigin := tx.origin
  let tf ← normalizeHolEquality t tf
  let tx ← normalizeHolEquality t tx
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
          (t.origin.join tfOrigin).join txOrigin⟩
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

def expandForDeduct (t : Theory) (th : Thm t) : Thm t :=
  match expandHolEquality t th with
  | .ok result => result
  | .error _ => th

def DEDUCT_ANTISYM (t : Theory) (th1 th2 : Thm t) : Thm t := Id.run do
  let th1 := expandForDeduct t th1
  let th2 := expandForDeduct t th2
  let p := th1.conclusion
  let q := th2.conclusion
  let hs := th1.assumptions.filter (fun h => decide (¬ h.Equivalent q))
  let ks := th2.assumptions.filter (fun h => decide (¬ h.Equivalent p))
  let d1 : Derivable t hs (.imp q p) := .disch q th1.derivation
  let d2 : Derivable t ks (.imp p q) := .disch p th2.derivation
  let ax : Derivable t [] (impAntisym p q) := .booleanAxiom (.impAntisym p q)
  let both : Derivable t (ks ++ hs) (.equal p q) := by
    simpa only [List.nil_append] using Derivable.mp (Derivable.mp ax d2) d1
  let assumptions := unionAssumptions hs ks
  let derivation : Derivable t assumptions (.equal p q) :=
    .context (fun r => by
      simpa only [assumptions, List.mem_append] using
        mem_unionAssumptions_swap (a := hs) (b := ks) (x := r)) both
  return ⟨assumptions, .equal p q, derivation,
    (t.origin.join th1.origin).join th2.origin⟩

def SYM (t : Theory) (th : Thm t) : Except KernelError (Thm t) := do
  let thOrigin := th.origin
  let th ← normalizeHolEquality t th
  let e ← equationView th.conclusion
  have d : Derivable t th.assumptions (.equal e.left e.right) := by
    rw [← e.equation]; exact th.derivation
  return ⟨th.assumptions, .equal e.right e.left, .symm d, t.origin.join thOrigin⟩

def TRANS (t : Theory) (tl tr : Thm t) : Except KernelError (Thm t) := do
  let tlOrigin := tl.origin
  let trOrigin := tr.origin
  let tl ← normalizeHolEquality t tl
  let tr ← normalizeHolEquality t tr
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
        (t.origin.join tlOrigin).join trOrigin⟩
    else .error .termMismatch
  else .error .typeMismatch

def EQ_MP (t : Theory) (te tp : Thm t) : Except KernelError (Thm t) := do
  let teOrigin := te.origin
  let tpOrigin := tp.origin
  let te ← normalizeHolEquality t te
  let ⟨a, p, q, he⟩ ← equationView te.conclusion
  if ht : a = .bool then
    let antecedent : Term t.signature [] .bool := ht ▸ p
    let consequent : Term t.signature [] .bool := ht ▸ q
    let tp ← alignHolEqualityPremise t antecedent tp
    if hp : antecedent.Equivalent tp.conclusion then
      have de : Derivable t te.assumptions (.equal antecedent consequent) := by
        subst a
        rw [← he]; exact te.derivation
      have dp : Derivable t tp.assumptions antecedent := .conversion hp.symm tp.derivation
      let assumptions := unionAssumptions te.assumptions tp.assumptions
      let derivation : Derivable t assumptions consequent :=
        .context (fun r => by
          simpa only [assumptions, List.mem_append] using
            mem_unionAssumptions (a := te.assumptions) (b := tp.assumptions) (x := r)) (.eqMp de dp)
      return ⟨assumptions, consequent, derivation,
        (t.origin.join teOrigin).join tpOrigin⟩
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
