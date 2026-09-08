import HotaruKernel.TypeInstantiationSemantics

namespace HotaruKernel

theorem HolType.inst_vars_subset (a : HolType) (i : TypeSubst) :
    ∀ k ∈ a.vars, ∀ n ∈ ((HolType.var k).inst i).vars, n ∈ (a.inst i).vars := by
  induction a using HolType.rec
    (motive_2 := fun args => ∀ k ∈ HolType.varsArgs args,
      ∀ n ∈ ((HolType.var k).inst i).vars, n ∈ HolType.varsArgs (HolType.instArgs i args)) with
  | var k =>
    intro j hj n hn
    have he : j = k := List.mem_singleton.mp hj
    subst j
    exact hn
  | bool => intro _ h; cases h
  | fn a b ha hb =>
    intro k hk n hn
    rcases List.mem_append.mp hk with hk | hk
    · exact List.mem_append_left _ (ha k hk n hn)
    · exact List.mem_append_right _ (hb k hk n hn)
  | op name args ih => exact ih
  | nil k hk => cases hk
  | cons a args ha ih k hk n hn =>
    rcases List.mem_append.mp hk with hk | hk
    · exact List.mem_append_left _ (ha k hk n hn)
    · exact List.mem_append_right _ (ih k hk n hn)

def Term.typeVars {ctx : List HolType} : Term s ctx a → List String
  | .fvar _ a _ => a.vars
  | .bvar _ => a.vars
  | .const _ scheme i _ _ => (scheme.inst i).vars
  | .app f x => f.typeVars ++ x.typeVars
  | @Term.lam _ a _ _ _ b => a.vars ++ b.typeVars
  | .equal l r => l.typeVars ++ r.typeVars
  | .imp p q => p.typeVars ++ q.typeVars

theorem Term.type_vars_subset {ctx : List HolType} (t : Term s ctx a) :
    ∀ n ∈ a.vars, n ∈ t.typeVars := by
  induction t with
  | fvar => exact fun _ h => h
  | bvar => exact fun _ h => h
  | const => exact fun _ h => h
  | app f x ihf ihx =>
    exact fun n hn => List.mem_append_left _ (ihf n (List.mem_append_right _ hn))
  | lam hv b ih =>
    intro n hn
    rcases List.mem_append.mp hn with hn | hn
    · exact List.mem_append_left _ hn
    · exact List.mem_append_right _ (ih n hn)
  | equal => intro n hn; cases hn
  | imp => intro n hn; cases hn

theorem PolymorphicModel.instanceValue_support (p : PolymorphicModel s)
    (m₁ m₂ : TypeModel) (h₁ : m₁.typeOp = p.typeOp) (h₂ : m₂.typeOp = p.typeOp)
    (n : QName) (scheme : HolType) (hd : s.constants.lookup n = some scheme) (i : TypeSubst)
    (hv : ∀ k ∈ (scheme.inst i).vars, m₁.typeVar k = m₂.typeVar k) :
    HEq (p.instanceValue m₁ h₁ n scheme hd i) (p.instanceValue m₂ h₂ n scheme hd i) := by
  apply (p.instanceValue_heq m₁ h₁ n scheme hd i).trans
  apply HEq.trans _ (p.instanceValue_heq m₂ h₂ n scheme hd i).symm
  apply p.constant_support
  intro k hk
  apply m₁.interp_congr_vars m₂ (h₁.trans h₂.symm)
  exact fun j hj => hv j (scheme.inst_vars_subset i k hk j hj)

theorem Term.eval_typeVars {ctx : List HolType} (t : Term s ctx a)
    (p : PolymorphicModel s) (m₁ m₂ : TypeModel)
    (h₁ : m₁.typeOp = p.typeOp) (h₂ : m₂.typeOp = p.typeOp)
    (f : FreeEnv (p.atTypes m₁ h₁)) (g : FreeEnv (p.atTypes m₂ h₂))
    (d : BoundEnv (p.atTypes m₁ h₁) ctx) (e : BoundEnv (p.atTypes m₂ h₂) ctx)
    (hv : ∀ k ∈ t.typeVars, m₁.typeVar k = m₂.typeVar k)
    (hf : ∀ n a, (n, a) ∈ t.freeVars → HEq (f a n) (g a n))
    (he : ∀ a (v : BVar ctx a), HEq (d v) (e v)) :
    HEq (t.eval (p.atTypes m₁ h₁) f d) (t.eval (p.atTypes m₂ h₂) g e) := by
  have hop := h₁.trans h₂.symm
  induction t with
  | fvar n a valid => exact hf n a (List.mem_cons_self ..)
  | bvar v => exact he _ v
  | const n scheme i hd valid =>
    change HEq ((p.atTypes m₁ h₁).constant n (scheme.inst i) _)
      ((p.atTypes m₂ h₂).constant n (scheme.inst i) _)
    rw [p.atTypes_constant, p.atTypes_constant]
    exact p.instanceValue_support m₁ m₂ h₁ h₂ n scheme hd i hv
  | @app a b ctx f' x ihf ihx =>
    have hvf := fun k hk => hv k (List.mem_append_left _ hk)
    have hvx := fun k hk => hv k (List.mem_append_right _ hk)
    apply ValueEquality.apply
      (m₁.interp_congr_vars m₂ hop a (fun k hk => hvx k (x.type_vars_subset k hk)))
      (m₁.interp_congr_vars m₂ hop b
        (fun k hk => hvf k (f'.type_vars_subset k (List.mem_append_right _ hk))))
    · exact ihf d e hvf (fun n a hn => hf n a (List.mem_append_left _ hn)) he
    · exact ihx d e hvx (fun n a hn => hf n a (List.mem_append_right _ hn)) he
  | @lam a b ctx valid body ih =>
    have hvb := fun k hk => hv k (List.mem_append_right _ hk)
    apply ValueEquality.funext
      (m₁.interp_congr_vars m₂ hop a (fun k hk => hv k (List.mem_append_left _ hk)))
      (m₁.interp_congr_vars m₂ hop b (fun k hk => hvb k (body.type_vars_subset k hk)))
    intro x y hxy
    apply ih (d.cons x) (e.cons y) hvb hf
    intro a v
    cases v with
    | zero => exact hxy
    | succ v => exact he _ v
  | @equal a ctx l r ihl ihr =>
    have hvl := fun k hk => hv k (List.mem_append_left _ hk)
    have hvr := fun k hk => hv k (List.mem_append_right _ hk)
    apply ValueEquality.decideEqual
      (m₁.interp_congr_vars m₂ hop a (fun k hk => hvl k (l.type_vars_subset k hk)))
    · exact ihl d e hvl (fun n a hn => hf n a (List.mem_append_left _ hn)) he
    · exact ihr d e hvr (fun n a hn => hf n a (List.mem_append_right _ hn)) he
  | imp l r ihl ihr =>
    apply heq_of_eq
    apply congrArg₂ (fun a b : Bool => !a || b)
    · exact eq_of_heq (ihl d e (fun k hk => hv k (List.mem_append_left _ hk))
        (fun n a hn => hf n a (List.mem_append_left _ hn)) he)
    · exact eq_of_heq (ihr d e (fun k hk => hv k (List.mem_append_right _ hk))
        (fun n a hn => hf n a (List.mem_append_right _ hn)) he)

noncomputable def Term.closedValue (t : Closed s a) (p : PolymorphicModel s)
    (m : TypeModel) (hm : m.typeOp = p.typeOp) : m.interp a :=
  t.eval (p.atTypes m hm) (fun a _ => Classical.choice (m.interp_nonempty a)) BoundEnv.nil

theorem Term.closedValue_eq_eval (t : Closed s a) (closed : t.freeVars = [])
    (p : PolymorphicModel s) (m : TypeModel) (hm : m.typeOp = p.typeOp)
    (f : FreeEnv (p.atTypes m hm)) :
    t.closedValue p m hm = t.eval (p.atTypes m hm) f BoundEnv.nil := by
  apply t.eval_free_congr
  intro n a hv
  rw [closed] at hv
  cases hv

theorem Term.closedValue_support (t : Closed s a) (closed : t.freeVars = [])
    (p : PolymorphicModel s) (m₁ m₂ : TypeModel)
    (h₁ : m₁.typeOp = p.typeOp) (h₂ : m₂.typeOp = p.typeOp)
    (hv : ∀ k ∈ t.typeVars, m₁.typeVar k = m₂.typeVar k) :
    HEq (t.closedValue p m₁ h₁) (t.closedValue p m₂ h₂) := by
  apply t.eval_typeVars p m₁ m₂ h₁ h₂ _ _ BoundEnv.nil BoundEnv.nil hv
  · intro n a hf
    rw [closed] at hf
    cases hf
  · intro a v
    cases v

theorem Term.closedValue_congr (t : Closed s a) (p q : PolymorphicModel s) (he : p = q)
    (m : TypeModel) (hp : m.typeOp = p.typeOp) (hq : m.typeOp = q.typeOp) :
    t.closedValue p m hp = t.closedValue q m hq := by
  cases he
  rfl

end HotaruKernel
