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
