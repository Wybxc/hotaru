import HotaruKernel.TypeDefinition
import HotaruKernel.TypeParameters

namespace HotaruKernel.TypeDefinition

variable {t : Theory}

noncomputable def carrier (d : TypeDefinition t) (p : PolymorphicModel t.signature)
    (args : List Type) : Type := by
  classical
  exact if hne : ∀ A ∈ args, Nonempty A then
    let m := p.parameterModel d.parameters args hne
    {x : m.interp d.representation // d.predicate.closedValue p m rfl x = true}
  else Unit

theorem carrier_nonempty (d : TypeDefinition t) (p : PolymorphicModel t.signature)
    (hp : Models t p) (args : List Type) : Nonempty (d.carrier p args) := by
  classical
  unfold carrier
  split
  · rename_i hne
    let m := p.parameterModel d.parameters args hne
    obtain ⟨x, hx⟩ := d.predicate_nonempty p hp m rfl
      (fun a _ => Classical.choice (m.interp_nonempty a))
    exact ⟨⟨x, hx⟩⟩
  · exact ⟨()⟩

noncomputable def operators (d : TypeDefinition t) (p : PolymorphicModel t.signature)
    (hp : Models t p) : p.OperatorExtension where
  typeOp name args := if name = d.name then d.carrier p args else p.typeOp name args
  op_nonempty name args hne := by
    split
    · exact d.carrier_nonempty p hp args
    · exact p.op_nonempty name args hne
  agrees name arity hd args _ := by
    have hn : name ≠ d.name := by intro he; subst name; rw [d.fresh] at hd; cases hd
    simp only [hn, ↓reduceIte]

noncomputable def interpretation (d : TypeDefinition t) (p : PolymorphicModel t.signature)
    (hp : Models t p) : PolymorphicModel d.signature :=
  (d.operators p hp).interpretation d.wellFormed rfl

theorem old_models (d : TypeDefinition t) (p : PolymorphicModel t.signature)
    (hp : Models t p) :
    Models (t.withSignature d.signature d.extendsSignature) (d.interpretation p hp) :=
  t.models_changeOperators p hp (d.operators p hp) d.wellFormed d.extendsSignature rfl

theorem subtype_eq {A B : Type} (f : A → Bool) (g : B → Bool) (h : A = B)
    (hf : HEq f g) : {x : A // f x = true} = {y : B // g y = true} := by
  cases h
  cases eq_of_heq hf
  rfl

theorem carrier_parameters (d : TypeDefinition t) (p : PolymorphicModel t.signature)
    (m : TypeModel) (hm : m.typeOp = p.typeOp) :
    d.carrier p (d.parameters.map m.typeVar) =
      {x : m.interp d.representation // d.predicate.closedValue p m hm x = true} := by
  classical
  unfold carrier
  rw [dif_pos (m.parameters_nonempty d.parameters)]
  let pm := p.parameterModel d.parameters (d.parameters.map m.typeVar)
    (m.parameters_nonempty d.parameters)
  have hv : ∀ k ∈ d.predicate.typeVars, pm.typeVar k = m.typeVar k :=
    fun k hk => p.parameterModel_var d.parameters m k (d.supported k hk)
  have ht : pm.interp d.representation = m.interp d.representation :=
    pm.interp_congr_vars m hm.symm _ (fun k hk =>
      hv k (d.predicate.type_vars_subset k (List.mem_append_left _ hk)))
  exact subtype_eq _ _ ht (d.predicate.closedValue_support d.closed p pm m rfl hm hv)

theorem interp_type (d : TypeDefinition t) (p : PolymorphicModel t.signature)
    (hp : Models t p) (m : TypeModel) (hm : m.typeOp = (d.operators p hp).typeOp) :
    m.interp d.type = d.carrier p (d.parameters.map m.typeVar) := by
  rw [type, TypeModel.interp_op, List.map_map]
  change m.typeOp d.name (d.parameters.map m.typeVar) = _
  rw [hm]
  simp only [operators, ↓reduceIte]

theorem interpretation_agrees (d : TypeDefinition t) (p : PolymorphicModel t.signature)
    (hp : Models t p) (m : TypeModel) (hm : m.typeOp = (d.interpretation p hp).typeOp) :
    Model.Agrees t.signature (p.atTypes (p.oldTypes m) rfl)
      ((d.interpretation p hp).atTypes m hm) :=
  (d.operators p hp).models_agree (u := d.signature) d.wellFormed rfl m hm

theorem predicate_value (d : TypeDefinition t) (p : PolymorphicModel t.signature)
    (hp : Models t p) (m : TypeModel) (hm : m.typeOp = (d.interpretation p hp).typeOp)
    (f : FreeEnv ((d.interpretation p hp).atTypes m hm)) :
    HEq (d.predicate.closedValue p (p.oldTypes m) rfl)
      ((d.predicate.rebase d.extendsSignature).eval
        ((d.interpretation p hp).atTypes m hm) f BoundEnv.nil) := by
  apply d.predicate.eval_agrees d.extendsSignature _ _ (d.interpretation_agrees p hp m hm)
    _ f BoundEnv.nil BoundEnv.nil (fun _ h => by cases h)
  · intro name a ha
    rw [d.closed] at ha
    cases ha
  · intro a v
    cases v

theorem interpreted_subtype (d : TypeDefinition t) (p : PolymorphicModel t.signature)
    (hp : Models t p) (m : TypeModel) (hm : m.typeOp = (d.interpretation p hp).typeOp)
    (f : FreeEnv ((d.interpretation p hp).atTypes m hm)) :
    m.interp d.type = {x : m.interp d.representation //
      (d.predicate.rebase d.extendsSignature).eval
        ((d.interpretation p hp).atTypes m hm) f BoundEnv.nil x = true} := by
  apply (d.interp_type p hp m hm).trans
  apply (d.carrier_parameters p (p.oldTypes m) rfl).trans
  exact subtype_eq _ _ ((d.interpretation_agrees p hp m hm).types.interp _ d.representationValid)
    (d.predicate_value p hp m hm f)

theorem representation_of_carrier_eq {B : Type} (A : Type) (p : B → Bool)
    (h : A = {x : B // p x = true}) :
    ∃ r : A → B, Function.Injective r ∧ ∀ y, p y = true ↔ ∃ x, y = r x := by
  cases h
  exact subtype_representation p

theorem formula_valid (d : TypeDefinition t) (p : PolymorphicModel t.signature)
    (hp : Models t p) (m : TypeModel) (hm : m.typeOp = (d.interpretation p hp).typeOp)
    (f : FreeEnv ((d.interpretation p hp).atTypes m hm)) :
    d.formula.eval ((d.interpretation p hp).atTypes m hm) f BoundEnv.nil = true := by
  apply (Term.eval_typeDefinitionT _ _ _ _ _ _ _).mpr
  exact representation_of_carrier_eq _ _ (d.interpreted_subtype p hp m hm f)

theorem interpretation_models (d : TypeDefinition t) (p : PolymorphicModel t.signature)
    (hp : Models t p) : Models d.target (d.interpretation p hp) := by
  intro m hm f q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact d.formula_valid p hp m hm f
  · exact d.old_models p hp m hm f q hq

theorem model_extension (d : TypeDefinition t) (p : PolymorphicModel t.signature)
    (hp : Models t p) :
    ∃ q : PolymorphicModel d.target.signature, Models d.target q ∧
      ∀ (m : TypeModel) (hm : m.typeOp = q.typeOp),
        Model.Agrees t.signature (p.atTypes (p.oldTypes m) rfl) (q.atTypes m hm) :=
  ⟨d.interpretation p hp, d.interpretation_models p hp, d.interpretation_agrees p hp⟩

end HotaruKernel.TypeDefinition
