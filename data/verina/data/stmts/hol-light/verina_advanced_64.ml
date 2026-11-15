(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_64,
  catalog title "removeElement": a deterministic recursive filter removes
  every occurrence of a target natural number while preserving the order of
  all remaining list elements, together with its full correctness contract.
  This file contains no proof.
*)

let removeElement_precond = new_definition
  `removeElement_precond (lst:num list) (target:num) <=> T`;;

let removeElement_helper =
  new_recursive_definition list_RECURSION
    `(!target:num.
        removeElement_helper ([]:num list) target = []) /\
     (!x:num. !xs:num list. !target:num.
        removeElement_helper (CONS x xs) target =
        let rest = removeElement_helper xs target in
        if x = target then rest else CONS x rest)`;;

let removeElement = new_definition
  `removeElement (lst:num list) (target:num) =
     removeElement_helper lst target`;;

let removeElement_getOpt = new_definition
  `removeElement_getOpt (xs:num list) (index:num) =
     if index < LENGTH xs then SOME (EL index xs)
     else (NONE:num option)`;;

let removeElement_indexedAll =
  new_recursive_definition list_RECURSION
    `(!filtered:num list. !index:num.
        removeElement_indexedAll
          filtered ([]:num list) index <=> T) /\
     (!x:num. !xs:num list. !filtered:num list. !index:num.
        removeElement_indexedAll
          filtered (CONS x xs) index <=>
        removeElement_getOpt filtered index = SOME x /\
        removeElement_indexedAll filtered xs (index + 1))`;;

let removeElement_postcond = new_definition
  `removeElement_postcond
      (lst:num list) (target:num) (result:num list) <=>
     let lst' = FILTER (\x:num. ~(x = target)) lst in
     removeElement_indexedAll lst' result 0 /\
     LENGTH result = LENGTH lst'`;;

let removeElement_spec_satisfied =
  `!lst:num list. !target:num.
     removeElement_precond lst target
     ==> removeElement_postcond
           lst target (removeElement lst target)`;;
