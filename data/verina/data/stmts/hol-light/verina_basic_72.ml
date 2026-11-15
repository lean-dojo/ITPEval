(*
  Statement-only formalization of VERINA corpus artifact verina_basic_72
  (verina__hol-light__verina_basic_72), catalog title "append": an executable
  copy-and-push operation appends one integer to an arbitrary integer array,
  together with its total precondition and exact pointwise, final-element, and
  length correctness contract. This file contains no proof.
*)

let append_precond = new_definition
  `append_precond (a:int list) (b:int) <=> T`;;

let append_getDefault = new_definition
  `append_getDefault (xs:int list) (i:num) =
     if i < LENGTH xs then EL i xs else (&0:int)`;;

let append_copyFuel =
  new_recursive_definition num_RECURSION
    `(!a:int list. !i:num. !acc:int list.
        append_copyFuel 0 a i acc = acc) /\
     (!fuel:num. !a:int list. !i:num. !acc:int list.
        append_copyFuel (SUC fuel) a i acc =
        if i < LENGTH a then
          append_copyFuel fuel a (i + 1)
            (APPEND acc (CONS (append_getDefault a i) []))
        else
          acc)`;;

let copy = new_definition
  `copy (a:int list) (i:num) (acc:int list) =
     append_copyFuel (LENGTH a - i) a i acc`;;

let append = new_definition
  `append (a:int list) (b:int) =
     let c_initial = copy a 0 ([]:int list) in
     let c_full = APPEND c_initial (CONS b []) in
     c_full`;;

let append_postcond = new_definition
  `append_postcond
      (a:int list) (b:int) (result:int list) <=>
     (!i:num.
        i < LENGTH a
        ==> append_getDefault result i = append_getDefault a i) /\
     append_getDefault result (LENGTH a) = b /\
     LENGTH result = LENGTH a + 1`;;

let append_spec_satisfied =
  `!a:int list. !b:int.
     append_precond a b
     ==> append_postcond a b (append a b)`;;
