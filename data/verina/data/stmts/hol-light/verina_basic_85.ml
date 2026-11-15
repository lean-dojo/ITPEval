(*
  Statement-only formalization of VERINA corpus artifact verina_basic_85
  (verina__hol-light__verina_basic_85), catalog title "reverse": an executable
  symmetric-swap traversal reverses an arbitrary integer array, together with
  its total precondition and exact length-and-index correctness contract. This
  file contains no proof.
*)

let reverse_precond = new_definition
  `reverse_precond (a:int list) <=> T`;;

let reverse_getDefault = new_definition
  `reverse_getDefault (a:int list) (i:num) =
     if i < LENGTH a then EL i a else (&0:int)`;;

let reverse_setAt =
  new_recursive_definition list_RECURSION
    `(!i:num. !value:int.
        reverse_setAt ([]:int list) i value = []) /\
     (!x:int. !xs:int list. !i:num. !value:int.
        reverse_setAt (CONS x xs) i value =
        if i = 0 then CONS value xs
        else CONS x (reverse_setAt xs (PRE i) value))`;;

let reverse_coreFuel =
  new_recursive_definition num_RECURSION
    `(!arr:int list. !i:num.
        reverse_coreFuel 0 arr i = arr) /\
     (!fuel:num. !arr:int list. !i:num.
        reverse_coreFuel (SUC fuel) arr i =
        if i < LENGTH arr DIV 2 then
          let j = LENGTH arr - 1 - i in
          let temp = reverse_getDefault arr i in
          let arr' =
            reverse_setAt arr i (reverse_getDefault arr j) in
          let arr'' = reverse_setAt arr' j temp in
          reverse_coreFuel fuel arr'' (i + 1)
        else
          arr)`;;

let reverse_core = new_definition
  `reverse_core (arr:int list) (i:num) =
     reverse_coreFuel (LENGTH arr DIV 2 - i) arr i`;;

let reverse = new_definition
  `reverse (a:int list) = reverse_core a 0`;;

let reverse_postcond = new_definition
  `reverse_postcond (a:int list) (result:int list) <=>
     LENGTH result = LENGTH a /\
     (!i:num.
        i < LENGTH a
        ==> reverse_getDefault result i =
            reverse_getDefault a (LENGTH a - 1 - i))`;;

let reverse_spec_satisfied =
  `!a:int list.
     reverse_precond a
     ==> reverse_postcond a (reverse a)`;;
