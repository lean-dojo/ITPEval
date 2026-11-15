(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_40,
  catalog title "maxOfList": an executable recursive maximum computation on a
  nonempty list of natural numbers returns a member that bounds every element
  of the list. This file contains no proof.
*)

let maxOfList_precond = new_definition
  `maxOfList_precond (lst:num list) <=>
     0 < LENGTH lst`;;

let maxOfList_helper =
  new_recursive_definition list_RECURSION
    `(maxOfList_helper ([]:num list) = 0) /\
     (!x:num. !xs:num list.
        maxOfList_helper (CONS x xs) =
        if xs = [] then x
        else
          let maxTail = maxOfList_helper xs in
          if x > maxTail then x else maxTail)`;;

let maxOfList = new_definition
  `maxOfList (lst:num list) = maxOfList_helper lst`;;

let maxOfList_postcond = new_definition
  `maxOfList_postcond (lst:num list) (result:num) <=>
     MEM result lst /\
     ALL (\x:num. x <= result) lst`;;

let maxOfList_spec_satisfied =
  `!lst:num list.
     maxOfList_precond lst
     ==> maxOfList_postcond lst (maxOfList lst)`;;
