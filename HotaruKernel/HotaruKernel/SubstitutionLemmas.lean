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
