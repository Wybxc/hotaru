import HotaruKernel.Substitution
import HotaruKernel.Check

namespace HotaruKernel

@[simp] theorem Substitution.apply_equal (rs : Substitution s) (l r : Closed s a) :
    rs.apply (.equal l r) = .equal (rs.apply l) (rs.apply r) := rfl

@[simp] theorem Substitution.apply_app (rs : Substitution s)
    (f : Closed s (.fn a b)) (x : Closed s a) :
    rs.apply (.app f x) = .app (rs.apply f) (rs.apply x) := rfl

@[simp] theorem Substitution.apply_single_variable (r : Replacement s)
    (hv : s.validType r.type = true) :
    Substitution.apply [r] (.fvar r.name r.type hv) = r.value := by
  simp [apply, Term.substFree, lookup]

theorem Term.substFree_eq {ctx : List HolType} (t : Term s ctx a)
    (r : FreeSubst s ctx) (q : Renaming ctx ctx)
    (hr : ∀ n a hv, (n, a) ∈ t.freeVars → r n a hv = .fvar n a hv)
    (hq : ∀ a (v : BVar ctx a), q v = v) : t.substFree r q = t := by
  induction t with
  | fvar n a hv => exact hr n a hv (List.mem_cons_self ..)
  | bvar v => exact congrArg Term.bvar (hq _ v)
  | const => rfl
  | app f x ihf ihx =>
    exact congrArg₂ Term.app
      (ihf r q (fun n a hv h => hr n a hv (List.mem_append_left _ h)) hq)
      (ihx r q (fun n a hv h => hr n a hv (List.mem_append_right _ h)) hq)
  | equal l u ihl ihu =>
    exact congrArg₂ Term.equal
      (ihl r q (fun n a hv h => hr n a hv (List.mem_append_left _ h)) hq)
      (ihu r q (fun n a hv h => hr n a hv (List.mem_append_right _ h)) hq)
  | imp p u ihp ihu =>
    exact congrArg₂ Term.imp
      (ihp r q (fun n a hv h => hr n a hv (List.mem_append_left _ h)) hq)
      (ihu r q (fun n a hv h => hr n a hv (List.mem_append_right _ h)) hq)
  | lam hv b ih =>
    apply congrArg (Term.lam hv)
    apply ih r.lift q.lift
    · intro n a hv h
      change (r n a hv).weaken = _
      rw [hr n a hv h]
      rfl
    · intro a v
      cases v with
      | zero => rfl
      | succ v => exact congrArg BVar.succ (hq _ v)

theorem Substitution.apply_fresh (t : Closed s a) (r : Replacement s)
    (h : (r.name, r.type) ∉ t.freeVars) : Substitution.apply [r] t = t := by
  apply t.substFree_eq
  · intro n a hv hm
    simp only [lookup]
    split
    · rename_i ht
      split
      · rename_i hn
        exact False.elim (h (by simpa [ht, hn] using hm))
      · rfl
    · rfl
  · exact fun _ _ => rfl

/-! A pair traversal shares the structural walk when two substitutions have
the same source and destination contexts. -/
def Term.substFreePair {ctx dst : List HolType} (left right : FreeSubst s dst)
    (q : Renaming ctx dst) : Term s ctx a → Term s dst a × Term s dst a
  | .fvar n a h => (left n a h, right n a h)
  | .bvar v => (.bvar (q v), .bvar (q v))
  | .const n t i h v => (.const n t i h v, .const n t i h v)
  | .app f x =>
      let f' := f.substFreePair left right q
      let x' := x.substFreePair left right q
      (.app f'.1 x'.1, .app f'.2 x'.2)
  | .lam h b =>
      let b' := b.substFreePair left.lift right.lift q.lift
      (.lam h b'.1, .lam h b'.2)
  | .equal l r =>
      let l' := l.substFreePair left right q
      let r' := r.substFreePair left right q
      (.equal l'.1 r'.1, .equal l'.2 r'.2)
  | .imp p q' =>
      let p' := p.substFreePair left right q
      let q'' := q'.substFreePair left right q
      (.imp p'.1 q''.1, .imp p'.2 q''.2)

theorem Term.substFreePair_fst {ctx dst : List HolType} (t : Term s ctx a)
    (left right : FreeSubst s dst) (q : Renaming ctx dst) :
    (t.substFreePair left right q).1 = t.substFree left q := by
  induction t generalizing dst with
  | fvar => rfl
  | bvar => rfl
  | const => rfl
  | app f x ihf ihx =>
      simp only [Term.substFreePair, Term.substFree, ihf, ihx]
  | lam h b ih =>
      simp only [Term.substFreePair, Term.substFree, ih]
  | equal l r ihl ihr =>
      simp only [Term.substFreePair, Term.substFree, ihl, ihr]
  | imp p q ihp ihq =>
      simp only [Term.substFreePair, Term.substFree, ihp, ihq]

theorem Term.substFreePair_snd {ctx dst : List HolType} (t : Term s ctx a)
    (left right : FreeSubst s dst) (q : Renaming ctx dst) :
    (t.substFreePair left right q).2 = t.substFree right q := by
  induction t generalizing dst with
  | fvar => rfl
  | bvar => rfl
  | const => rfl
  | app f x ihf ihx =>
      simp only [Term.substFreePair, Term.substFree, ihf, ihx]
  | lam h b ih =>
      simp only [Term.substFreePair, Term.substFree, ih]
  | equal l r ihl ihr =>
      simp only [Term.substFreePair, Term.substFree, ihl, ihr]
  | imp p q ihp ihq =>
      simp only [Term.substFreePair, Term.substFree, ihp, ihq]

def nameBound : List FVar → Nat
  | [] => 0
  | (n, _) :: vs => n.length + nameBound vs

theorem length_le_nameBound (n : String) (a : HolType) (vs : List FVar)
    (h : (n, a) ∈ vs) : n.length ≤ nameBound vs := by
  induction vs with
  | nil => cases h
  | cons v vs ih =>
    rcases List.mem_cons.mp h with h | h
    · cases h
      exact Nat.le_add_right _ _
    · have hi := ih h
      simp only [nameBound]
      omega

def freshName (vs : List FVar) : String :=
  String.ofList (List.replicate (nameBound vs + 1) 'x')

theorem freshName_not_mem (vs : List FVar) (a : HolType) : (freshName vs, a) ∉ vs := by
  intro h
  have hl := length_le_nameBound (freshName vs) a vs h
  simp only [freshName, String.length_ofList, List.length_replicate] at hl
  omega

end HotaruKernel
