mutual
/-- HOL types.
    The `app` variant is defined with a mutual inductive `HOLTypeList` to avoid issues with nested inductives. -/
inductive HOLType
| var : String -> HOLType
| app : String -> HOLTypeList -> HOLType
deriving Repr, DecidableEq
inductive HOLTypeList
| nil : HOLTypeList
| cons : HOLType -> HOLTypeList -> HOLTypeList
deriving Repr, DecidableEq
end

instance : Inhabited HOLTypeList where
    default := .nil

instance : Inhabited HOLType where
    default := .var "a"

@[simp] def HOLTypeList.toList : HOLTypeList -> List HOLType
| .nil => []
| .cons h t => h :: toList t

@[simp] def HOLTypeList.fromList : List HOLType -> HOLTypeList
| [] => .nil
| h :: t => .cons h (fromList t)

/-- Boolean type. -/
abbrev HOLType.bool : HOLType := .var "bool"
/-- Make a function type `x -> y`. -/
abbrev HOLType.fun (x y : HOLType) : HOLType := .app "fun" (.fromList [x, y])

mutual
/-- Type substitution: given an instaniation `i` mapping type variables to types, apply it to a type. -/
def typeSubst (i : List (String × HOLType)) : HOLType → HOLType
| .var x => match i.find? (fun (y, _) => y = x) with
    | some (_, T) => T
    | none => .var x
| .app c args => .app c (typeListSubst i args)

def typeListSubst (i : List (String × HOLType)) : HOLTypeList → HOLTypeList
| .nil => .nil
| .cons h t => .cons (typeSubst i h) (typeListSubst i t)
end

/-- If `ty0` instantiates to `ty` under some substitution, then `ty` is an instance of `ty0`. -/
def HOLType.IsInstance (ty ty0 : HOLType) : Prop :=
  ∃ i, typeSubst i ty0 = ty
