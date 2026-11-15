(*
  Statement-only formalization of VERINA corpus artifact verina_basic_58
  (verina__hol-light__verina_basic_58), catalog title
  "double_array_elements": an executable indexed traversal doubles every
  integer in an array using values from the original array, together with its
  total precondition and length-and-pointwise correctness contract. This file
  contains no proof.
*)

let double_array_elements_precond = new_definition
  `double_array_elements_precond (s:int list) <=> T`;;

let double_array_elements_getDefault = new_definition
  `double_array_elements_getDefault (s:int list) (i:num) =
     if i < LENGTH s then EL i s else (&0:int)`;;

let double_array_elements_setAt =
  new_recursive_definition list_RECURSION
    `(!i:num. !value:int.
        double_array_elements_setAt ([]:int list) i value = []) /\
     (!x:int. !xs:int list. !i:num. !value:int.
        double_array_elements_setAt (CONS x xs) i value =
        if i = 0 then CONS value xs
        else
          CONS x
            (double_array_elements_setAt xs (PRE i) value))`;;

let double_array_elements_loopFuel =
  new_recursive_definition num_RECURSION
    `(!s_old:int list. !s:int list. !i:num.
        double_array_elements_loopFuel 0 s_old s i = s) /\
     (!fuel:num. !s_old:int list. !s:int list. !i:num.
        double_array_elements_loopFuel
          (SUC fuel) s_old s i =
        if i < LENGTH s then
          let new_s =
            double_array_elements_setAt s i
              ((&2:int) *
               double_array_elements_getDefault s_old i) in
          double_array_elements_loopFuel
            fuel s_old new_s (i + 1)
        else
          s)`;;

let double_array_elements_aux = new_definition
  `double_array_elements_aux
      (s_old:int list) (s:int list) (i:num) =
     double_array_elements_loopFuel
       (LENGTH s - i) s_old s i`;;

let double_array_elements = new_definition
  `double_array_elements (s:int list) =
     double_array_elements_aux s s 0`;;

let double_array_elements_postcond = new_definition
  `double_array_elements_postcond
      (s:int list) (result:int list) <=>
     LENGTH result = LENGTH s /\
     (!i:num.
        i < LENGTH s
        ==> EL i result = (&2:int) * EL i s)`;;

let double_array_elements_spec_satisfied =
  `!s:int list.
     double_array_elements_precond s
     ==> double_array_elements_postcond
           s (double_array_elements s)`;;
