(*
  Statement-only formalization of VERINA corpus artifact verina_basic_9
  (verina__hol-light__verina_basic_9), catalog title "hasCommonElement": an
  executable nested scan decides whether two nonempty integer arrays share an
  element, together with its exact Boolean correctness contract. This file
  contains no proof.
*)

let hasCommonElement_precond = new_definition
  `hasCommonElement_precond (a:int list) (b:int list) <=>
     LENGTH a > 0 /\ LENGTH b > 0`;;

let hasCommonElement_anyEq =
  new_recursive_definition list_RECURSION
    `(hasCommonElement_anyEq (x:int) ([]:int list) = F) /\
     (!x:int. !y:int. !ys:int list.
        hasCommonElement_anyEq x (CONS y ys) =
        if x = y then T else hasCommonElement_anyEq x ys)`;;

let hasCommonElement =
  new_recursive_definition list_RECURSION
    `(!b:int list.
        hasCommonElement ([]:int list) b = F) /\
     (!x:int. !xs:int list. !b:int list.
        hasCommonElement (CONS x xs) b =
        if hasCommonElement_anyEq x b
        then T
        else hasCommonElement xs b)`;;

let hasCommonElement_postcond = new_definition
  `hasCommonElement_postcond
      (a:int list) (b:int list) (result:bool) <=>
     ((?i:num. ?j:num.
         i < LENGTH a /\
         j < LENGTH b /\
         EL i a = EL j b) <=>
      result)`;;

let hasCommonElement_spec_satisfied =
  `!a:int list. !b:int list.
     hasCommonElement_precond a b
     ==> hasCommonElement_postcond
           a b (hasCommonElement a b)`;;
