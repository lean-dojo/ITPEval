(*
  Statement-only formalization of VERINA corpus artifact verina_basic_77
  (verina__hol-light__verina_basic_77), catalog title
  "modify_array_element": an executable nested natural-number array update
  replaces one selected inner element while preserving the array structure
  and all other entries. This file contains no proof.
*)

let modify_array_element_precond = new_definition
  `modify_array_element_precond
      (arr:(num list)list) (index1:num) (index2:num) (val:num) <=>
     index1 < LENGTH arr /\
     index2 < LENGTH (EL index1 arr)`;;

let updateInner =
  new_recursive_definition list_RECURSION
    `(!idx:num. !val:num.
        updateInner ([]:num list) idx val = []) /\
     (!x:num. !xs:num list. !idx:num. !val:num.
        updateInner (CONS x xs) idx val =
        if idx = 0 then CONS val xs
        else CONS x (updateInner xs (PRE idx) val))`;;

let modify_array_element_setRow =
  new_recursive_definition list_RECURSION
    `(!idx:num. !row:num list.
        modify_array_element_setRow
          ([]:(num list)list) idx row = []) /\
     (!x:num list. !xs:(num list)list. !idx:num. !row:num list.
        modify_array_element_setRow (CONS x xs) idx row =
        if idx = 0 then CONS row xs
        else
          CONS x
            (modify_array_element_setRow xs (PRE idx) row))`;;

let modify_array_element = new_definition
  `modify_array_element
      (arr:(num list)list) (index1:num) (index2:num) (val:num) =
     let inner = EL index1 arr in
     let inner' = updateInner inner index2 val in
     modify_array_element_setRow arr index1 inner'`;;

let modify_array_element_postcond = new_definition
  `modify_array_element_postcond
      (arr:(num list)list) (index1:num) (index2:num) (val:num)
      (result:(num list)list) <=>
     LENGTH result = LENGTH arr /\
     LENGTH (EL index1 result) = LENGTH (EL index1 arr) /\
     (!i:num.
        i < LENGTH arr
        ==> ~(i = index1)
        ==> EL i result = EL i arr) /\
     (!j:num.
        j < LENGTH (EL index1 arr)
        ==> ~(j = index2)
        ==> EL j (EL index1 result) = EL j (EL index1 arr)) /\
     EL index2 (EL index1 result) = val`;;

let modify_array_element_spec_satisfied =
  `!arr:(num list)list. !index1 index2 val:num.
     modify_array_element_precond arr index1 index2 val
     ==> modify_array_element_postcond
           arr index1 index2 val
           (modify_array_element arr index1 index2 val)`;;
