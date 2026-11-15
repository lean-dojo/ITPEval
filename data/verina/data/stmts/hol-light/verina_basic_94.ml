(*
  Statement-only formalization of VERINA corpus artifact verina_basic_94
  (verina__hol-light__verina_basic_94), catalog title "iter_copy": an
  executable left-to-right traversal copies every integer array element into
  a fresh array, together with its total precondition and exact length-and-
  pointwise correctness contract. This file contains no proof.
*)

let iter_copy_precond = new_definition
  `iter_copy_precond (s:int list) <=> T`;;

let iter_copy_loopFuel =
  new_recursive_definition num_RECURSION
    `(!s:int list. !i:num. !acc:int list.
        iter_copy_loopFuel 0 s i acc = acc) /\
     (!fuel:num. !s:int list. !i:num. !acc:int list.
        iter_copy_loopFuel (SUC fuel) s i acc =
        if i < LENGTH s then
          iter_copy_loopFuel fuel s (i + 1)
            (APPEND acc (CONS (EL i s) []))
        else
          acc)`;;

let iter_copy_loop = new_definition
  `iter_copy_loop (s:int list) (i:num) (acc:int list) =
     iter_copy_loopFuel (LENGTH s - i) s i acc`;;

let iter_copy = new_definition
  `iter_copy (s:int list) =
     iter_copy_loop s 0 ([]:int list)`;;

let iter_copy_postcond = new_definition
  `iter_copy_postcond (s:int list) (result:int list) <=>
     LENGTH s = LENGTH result /\
     (!i:num.
        i < LENGTH s
        ==> EL i s = EL i result)`;;

let iter_copy_spec_satisfied =
  `!s:int list.
     iter_copy_precond s
     ==> iter_copy_postcond s (iter_copy s)`;;
