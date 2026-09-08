import HotaruKernel.Foundation

namespace HotaruKernel.Foundation

noncomputable def choose {A : Type} (hne : Nonempty A) (p : A → Bool) : A := by
  classical
  exact if h : ∃ x, p x = true then Classical.choose h else Classical.choice hne

theorem choose_spec {A : Type} (hne : Nonempty A) (p : A → Bool) (x : A)
    (hx : p x = true) : p (choose hne p) = true := by
  classical
  simp only [choose, dif_pos (show ∃ x, p x = true from ⟨x, hx⟩)]
  exact Classical.choose_spec (show ∃ x, p x = true from ⟨x, hx⟩)

theorem choose_heq {A B : Type} (h : A = B) (ha : Nonempty A) (hb : Nonempty B) :
    HEq (choose ha) (choose hb) := by
  cases h
  rfl

theorem declared_scheme (name : QName) (a : HolType)
    (h : signature.constants.lookup name = some a) : a = selectType := by
  simp only [signature, List.lookup_cons, List.lookup_nil] at h
  split at h
  · exact (Option.some.inj h).symm
  · contradiction

noncomputable def choiceFamily (name : QName) (a : HolType)
    (h : signature.constants.lookup name = some a) (m : TypeModel) : m.interp a :=
  cast (congrArg m.interp (declared_scheme name a h).symm) (choose (m.var_nonempty "a"))

theorem choiceFamily_support (name : QName) (a : HolType)
    (h : signature.constants.lookup name = some a) (m n : TypeModel)
    (hv : ∀ k ∈ a.vars, m.typeVar k = n.typeVar k) :
    HEq (choiceFamily name a h m) (choiceFamily name a h n) := by
  have hs := declared_scheme name a h
  subst a
  simp only [choiceFamily, cast_eq]
  exact choose_heq (hv "a" (by simp [selectType, alpha, HolType.vars])) _ _

noncomputable def model : PolymorphicModel signature where
  typeOp := fun _ _ => Nat
  op_nonempty := fun _ _ _ => ⟨0⟩
  constant name a h m _ := choiceFamily name a h m
  constant_support name a h m n _ _ hv := choiceFamily_support name a h m n hv

theorem select_value {ctx : List HolType} (m : TypeModel) (hm : m.typeOp = model.typeOp)
    (f : FreeEnv (model.atTypes m hm)) (e : BoundEnv (model.atTypes m hm) ctx) :
    select.eval (model.atTypes m hm) f e = choose (m.var_nonempty "a") := by
  change (model.atTypes m hm).constant selectName (selectType.inst []) _ = _
  rw [model.atTypes_constant m hm selectName selectType (by decide +kernel) []]
  apply eq_of_heq
  apply (model.instanceValue_heq m hm selectName selectType (by decide +kernel) []).trans
  rfl

theorem select_valid (m : TypeModel) (hm : m.typeOp = model.typeOp)
    (f : FreeEnv (model.atTypes m hm)) :
    selectAxiom.eval (model.atTypes m hm) f BoundEnv.nil = true := by
  apply (Term.eval_forallT _ _ _ _ _).mpr
  intro p
  apply (Term.eval_forallT _ _ _ _ _).mpr
  intro x
  change ((!p x) || p (select.eval (model.atTypes m hm) f
    (BoundEnv.cons (a := alpha) x (BoundEnv.cons (a := .fn alpha .bool) p BoundEnv.nil)) p)) = true
  rw [select_value]
  cases hx : p x with
  | false => rfl
  | true =>
    change p (choose (m.var_nonempty "a") p) = true
    exact choose_spec _ p x hx

theorem ind_is_nat (m : TypeModel) (hm : m.typeOp = model.typeOp) : m.interp ind = Nat := by
  rw [ind, TypeModel.interp_op, hm]
  rfl

theorem infinity_valid (m : TypeModel) (hm : m.typeOp = model.typeOp)
    (f : FreeEnv (model.atTypes m hm)) :
    infinityAxiom.eval (model.atTypes m hm) f BoundEnv.nil = true := by
  apply (Term.eval_infiniteT _ _ _ _ _ _ _).mpr
  change ∃ r : m.interp ind → m.interp ind, Function.Injective r ∧ ¬ Function.Surjective r
  rw [ind_is_nat m hm]
  exact nat_infinity

theorem models : Models theory model := by
  intro m hm f q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact eta_valid _ _
  rcases List.mem_cons.mp hq with rfl | hq
  · exact select_valid m hm f
  rcases List.mem_cons.mp hq with rfl | hq
  · exact infinity_valid m hm f
  have he : q = boolCasesAxiom := List.mem_singleton.mp hq
  subst q
  exact boolCases_valid _ _

def types : TypeModel where
  typeVar := fun _ => Nat
  typeOp := fun _ _ => Nat
  var_nonempty := fun _ => ⟨0⟩
  op_nonempty := fun _ _ _ => ⟨0⟩

theorem falsehood_not_derivable : ¬ Derivable theory [] Term.falseT := by
  intro d
  have h := d.sound model models types rfl
    (fun a _ => Classical.choice (types.interp_nonempty a)) (fun _ h => by cases h)
  rw [Term.eval_falseT] at h
  cases h

end HotaruKernel.Foundation
