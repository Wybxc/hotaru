mutual
inductive HOLType
| var : String -> HOLType
| app : String -> HOLTypeList -> HOLType
deriving Repr, DecidableEq
inductive HOLTypeList
| nil : HOLTypeList
| cons : HOLType -> HOLTypeList -> HOLTypeList
deriving Repr, DecidableEq
end

def HOLTypeList.toList : HOLTypeList -> List HOLType
| .nil => []
| .cons h t => h :: toList t

def HOLTypeList.fromList : List HOLType -> HOLTypeList
| [] => .nil
| h :: t => .cons h (fromList t)

abbrev HOLType.bool : HOLType := .var "bool"
abbrev HOLType.fun (x y : HOLType) : HOLType := .app "fun" (.fromList [x, y])

mutual
def type_subst (i : List (String × HOLType)) : HOLType → HOLType
| .var x => match i.find? (fun (y, _) => y = x) with
    | some (_, T) => T
    | none => .var x
| .app c args => .app c (type_subst_list i args)

def type_subst_list (i : List (String × HOLType)) : HOLTypeList → HOLTypeList
| .nil => .nil
| .cons h t => .cons (type_subst i h) (type_subst_list i t)
end

def IsInstance (ty0 ty : HOLType) : Prop :=
  ∃ i, type_subst i ty0 = ty
