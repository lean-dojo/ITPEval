(*
  Statement-only formalization of VERINA corpus artifact verina_basic_32
  (verina__hol-light__verina_basic_32), catalog title "swapFirstAndLast": a
  deterministic program swaps the first and last elements of a nonempty
  integer array while preserving its size and every interior element. This
  file contains no proof.
*)

let swapFirstAndLast_getDefault = new_definition
  `swapFirstAndLast_getDefault (xs:int list) (i:num) =
     if i < LENGTH xs then EL i xs else (&0:int)`;;

let swapFirstAndLast_setAt =
  new_recursive_definition list_RECURSION
    `(!i:num. !value:int.
        swapFirstAndLast_setAt ([]:int list) i value = []) /\
     (!x:int. !xs:int list. !i:num. !value:int.
        swapFirstAndLast_setAt (CONS x xs) i value =
        if i = 0 then CONS value xs
        else CONS x
          (swapFirstAndLast_setAt xs (PRE i) value))`;;

let swapFirstAndLast_precond = new_definition
  `swapFirstAndLast_precond (a:int list) <=>
     0 < LENGTH a`;;

let swapFirstAndLast = new_definition
  `swapFirstAndLast (a:int list) =
     let first = swapFirstAndLast_getDefault a 0 in
     let last =
       swapFirstAndLast_getDefault a (LENGTH a - 1) in
     swapFirstAndLast_setAt
       (swapFirstAndLast_setAt a 0 last)
       (LENGTH a - 1)
       first`;;

let swapFirstAndLast_postcond = new_definition
  `swapFirstAndLast_postcond
      (a:int list) (result:int list) <=>
     LENGTH result = LENGTH a /\
     swapFirstAndLast_getDefault result 0 =
       swapFirstAndLast_getDefault a (LENGTH a - 1) /\
     swapFirstAndLast_getDefault
       result (LENGTH result - 1) =
       swapFirstAndLast_getDefault a 0 /\
     (!i:num.
        i < LENGTH result - 2
        ==> swapFirstAndLast_getDefault result (i + 1) =
            swapFirstAndLast_getDefault a (i + 1))`;;

let swapFirstAndLast_spec_satisfied =
  `!a:int list.
     swapFirstAndLast_precond a
     ==> swapFirstAndLast_postcond
           a (swapFirstAndLast a)`;;
