import HotaruKernel.Syntax

/-! Full function-space semantics, independent of the inference system. -/
namespace HotaruKernel

variable {ctx dst : List HolType}

structure TypeModel where
  typeVar : String → Type
  typeOp : QName → List Type → Type
  var_nonempty : ∀ n, Nonempty (typeVar n)
  op_nonempty : ∀ n args, (∀ a ∈ args, Nonempty a) → Nonempty (typeOp n args)

noncomputable def TypeModel.interp (m : TypeModel) : HolType → Type :=
  HolType.rec (motive_1 := fun _ => Type) (motive_2 := fun _ => List Type)
    m.typeVar Bool (fun _ _ a b => a → b) (fun n _ args => m.typeOp n args)
    [] (fun _ _ a args => a :: args)

theorem TypeModel.interp_op (m : TypeModel) (n : QName) (args : List HolType) :
    m.interp (.op n args) = m.typeOp n (args.map m.interp) := by
  change m.typeOp n _ = _
  apply congrArg (m.typeOp n)
  induction args with
  | nil => rfl
  | cons a args ih => exact congrArg (fun xs => m.interp a :: xs) ih

theorem TypeModel.interp_nonempty (m : TypeModel) (a : HolType) : Nonempty (m.interp a) := by
  induction a using HolType.rec
    (motive_2 := fun args => ∀ a ∈ args, Nonempty (m.interp a)) with
  | var n => exact m.var_nonempty n
  | bool => exact ⟨true⟩
  | fn a b _ hb => exact hb.elim (fun y => ⟨fun _ => y⟩)
  | op n args ih =>
    rw [m.interp_op]
    apply m.op_nonempty
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact ih b hb
  | nil a h => cases h
  | cons a args ha ih b hb =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ha
    · exact ih b hb

structure Model (s : Signature) extends TypeModel where
  constant : (n : QName) → (a : HolType) →
    (∃ scheme i, s.constants.lookup n = some scheme ∧ scheme.inst i = a) →
    toTypeModel.interp a

abbrev Model.Val (m : Model s) (a : HolType) := m.toTypeModel.interp a
abbrev FreeEnv (m : Model s) := (a : HolType) → String → m.Val a
abbrev BoundEnv (m : Model s) (ctx : List HolType) := ∀ {a}, BVar ctx a → m.Val a

def BoundEnv.nil : BoundEnv m [] := fun v => nomatch v

def BoundEnv.cons (x : m.Val a) (e : BoundEnv m ctx) : BoundEnv m (a :: ctx)
  | _, .zero => x
  | _, .succ v => e v

noncomputable def Term.eval {ctx : List HolType}
    (m : Model s) (f : FreeEnv m) (e : BoundEnv m ctx) :
    Term s ctx a → m.Val a
  | .fvar n a _ => f a n
  | .bvar v => e v
  | .const n t i h _ => m.constant n (t.inst i) ⟨t, i, h, rfl⟩
  | .app g x => (g.eval m f e) (x.eval m f e)
  | .lam _ b => fun x => b.eval m f (e.cons x)
  | .equal l r => @decide (l.eval m f e = r.eval m f e) (Classical.propDecidable _)
  | .imp p q => !(p.eval m f e) || q.eval m f e

theorem Term.eval_rename (t : Term s ctx a) (m : Model s) (f : FreeEnv m)
    (r : Renaming ctx dst) (e : BoundEnv m ctx) (d : BoundEnv m dst)
    (h : ∀ a (v : BVar ctx a), d (r v) = e v) :
    (t.rename r).eval m f d = t.eval m f e := by
  induction t generalizing dst with
  | fvar => rfl
  | bvar v => exact h _ v
  | const => rfl
  | app g x hg hx => simp only [rename, eval, hg r e d h, hx r e d h]
  | imp p q hp hq => simp only [rename, eval, hp r e d h, hq r e d h]
  | equal l u hl hu =>
    simp only [rename, eval]
    rw [hl r e d h, hu r e d h]
  | lam valid b ih =>
    funext x
    apply ih r.lift (e.cons x) (d.cons x)
    intro a v
    cases v with
    | zero => rfl
    | succ v => exact h _ v

theorem Term.eval_weaken (t : Term s ctx a) (m : Model s) (f : FreeEnv m)
    (e : BoundEnv m ctx) (x : m.Val b) :
    t.weaken.eval m f (e.cons x) = t.eval m f e :=
  t.eval_rename m f _ e (e.cons x) (fun _ _ => rfl)

theorem Term.eval_substBound (t : Term s ctx a) (m : Model s) (f : FreeEnv m)
    (r : BoundSubst s ctx dst) (e : BoundEnv m ctx) (d : BoundEnv m dst)
    (h : ∀ a (v : BVar ctx a), (r v).eval m f d = e v) :
    (t.substBound r).eval m f d = t.eval m f e := by
  induction t generalizing dst with
  | fvar => rfl
  | bvar v => exact h _ v
  | const => rfl
  | app g x hg hx => simp only [substBound, eval, hg r e d h, hx r e d h]
  | imp p q hp hq => simp only [substBound, eval, hp r e d h, hq r e d h]
  | equal l u hl hu =>
    simp only [substBound, eval]
    rw [hl r e d h, hu r e d h]
  | lam valid b ih =>
    funext x
    apply ih r.lift (e.cons x) (d.cons x)
    intro a v
    cases v with
    | zero => rfl
    | succ v => exact (eval_weaken _ m f d x).trans (h _ v)

theorem Term.eval_open (t : Term s (a :: ctx) b) (x : Term s ctx a)
    (m : Model s) (f : FreeEnv m) (e : BoundEnv m ctx) :
    (t.open x).eval m f e = t.eval m f (e.cons (x.eval m f e)) := by
  apply t.eval_substBound
  intro a v
  cases v <;> rfl

theorem Term.eval_substFree (t : Term s ctx a) (m : Model s)
    (f g : FreeEnv m) (r : FreeSubst s dst) (q : Renaming ctx dst)
    (e : BoundEnv m ctx) (d : BoundEnv m dst)
    (hf : ∀ n a h, (r n a h).eval m g d = f a n)
    (hb : ∀ a (v : BVar ctx a), d (q v) = e v) :
    (t.substFree r q).eval m g d = t.eval m f e := by
  induction t generalizing dst with
  | fvar n a h => exact hf n a h
  | bvar v => exact hb _ v
  | const => rfl
  | app g x hg hx => simp only [substFree, eval, hg _ _ _ _ hf hb, hx _ _ _ _ hf hb]
  | imp p t hp ht => simp only [substFree, eval, hp r q e d hf hb, ht r q e d hf hb]
  | equal l u hl hu =>
    simp only [substFree, eval]
    rw [hl r q e d hf hb, hu r q e d hf hb]
  | lam valid b ih =>
    funext x
    apply ih r.lift q.lift (e.cons x) (d.cons x)
    · intro n a h
      exact (eval_weaken _ m g d x).trans (hf n a h)
    · intro a v
      cases v with
      | zero => rfl
      | succ v => exact hb _ v

def FreeEnv.set (f : FreeEnv m) (n : String) (a : HolType) (x : m.Val a) : FreeEnv m :=
  fun b k => if h : b = a then if k = n then h ▸ x else f b k else f b k

theorem Term.eval_replace (t : Term s ctx b) (replacement : Term s ctx a)
    (m : Model s) (f : FreeEnv m) (e : BoundEnv m ctx) (n : String) :
    (t.replace n a replacement).eval m f e =
      t.eval m (f.set n a (replacement.eval m f e)) e := by
  apply t.eval_substFree
  · intro k b h
    by_cases ht : b = a
    · subst b
      by_cases hn : k = n <;> simp [FreeSubst.single, FreeEnv.set, hn, eval]
    · simp [FreeSubst.single, FreeEnv.set, ht, eval]
  · intro a v
    rfl

theorem Term.eval_close (t : Term s ctx b) (m : Model s) (f : FreeEnv m)
    (e : BoundEnv m ctx) (n : String) (a : HolType) (x : m.Val a) :
    (t.close n a).eval m f (e.cons x) = t.eval m (f.set n a x) e := by
  apply t.eval_substFree
  · intro k b h
    by_cases ht : b = a
    · subst b
      by_cases hn : k = n <;> simp [FreeSubst.close, FreeEnv.set, hn, eval, BoundEnv.cons]
    · simp [FreeSubst.close, FreeEnv.set, ht, eval]
  · intro a v
    rfl

theorem Term.eval_free_congr (t : Term s ctx a) (m : Model s)
    (f g : FreeEnv m) (e : BoundEnv m ctx)
    (h : ∀ n a, (n, a) ∈ t.freeVars → f a n = g a n) :
    t.eval m f e = t.eval m g e := by
  induction t with
  | fvar n a valid => exact h n a (by simp [freeVars])
  | bvar => rfl
  | const => rfl
  | app t u ht hu =>
    simp only [eval]
    rw [ht e (fun n a hn => h n a (by simp [freeVars, hn])),
      hu e (fun n a hn => h n a (by simp [freeVars, hn]))]
  | equal t u ht hu =>
    simp only [eval]
    rw [ht e (fun n a hn => h n a (by simp [freeVars, hn])),
      hu e (fun n a hn => h n a (by simp [freeVars, hn]))]
  | imp t u ht hu =>
    simp only [eval]
    rw [ht e (fun n a hn => h n a (by simp [freeVars, hn])),
      hu e (fun n a hn => h n a (by simp [freeVars, hn]))]
  | lam valid b ih =>
    funext x
    exact ih (e.cons x) h

theorem Term.eval_set_of_not_free (t : Term s ctx b) (m : Model s)
    (f : FreeEnv m) (e : BoundEnv m ctx) (n : String) (a : HolType) (x : m.Val a)
    (h : (n, a) ∉ t.freeVars) : t.eval m (f.set n a x) e = t.eval m f e := by
  apply t.eval_free_congr
  intro k b hk
  by_cases ht : b = a
  · subst b
    have hn : k ≠ n := by intro he; subst k; exact h hk
    simp [FreeEnv.set, hn]
  · simp [FreeEnv.set, ht]

def Satisfies (m : Model s) (f : FreeEnv m) (hs : List (Formula s)) : Prop :=
  ∀ p ∈ hs, p.eval m f BoundEnv.nil = true

def Entails (s : Signature) (hs : List (Formula s)) (c : Formula s) : Prop :=
  ∀ (m : Model s) (f : FreeEnv m), Satisfies m f hs → c.eval m f BoundEnv.nil = true

end HotaruKernel
