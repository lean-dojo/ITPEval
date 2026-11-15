(*
  Statement-only formalization of VERINA corpus artifact verina_basic_68
  (verina__hol-light__verina_basic_68), catalog title "LinearSearch": an
  executable left-to-right scan of an integer array returns the first index
  containing the target, or the array length when the target is absent,
  together with its total precondition and exact correctness contract. This
  file contains no proof.
*)

let LinearSearch_precond = new_definition
  `LinearSearch_precond (a:int list) (e:int) <=> T`;;

let LinearSearch_loop =
  new_recursive_definition list_RECURSION
    `(!e:int. !n:num.
        LinearSearch_loop ([]:int list) e n = n) /\
     (!x:int. !xs:int list. !e:int. !n:num.
        LinearSearch_loop (CONS x xs) e n =
        if x = e then n
        else LinearSearch_loop xs e (SUC n))`;;

let LinearSearch = new_definition
  `LinearSearch (a:int list) (e:int) =
     LinearSearch_loop a e 0`;;

let LinearSearch_getDefault = new_definition
  `LinearSearch_getDefault (a:int list) (i:num) =
     if i < LENGTH a then EL i a else (&0:int)`;;

let LinearSearch_postcond = new_definition
  `LinearSearch_postcond
      (a:int list) (e:int) (result:num) <=>
     result <= LENGTH a /\
     (result = LENGTH a \/
      LinearSearch_getDefault a result = e) /\
     (!i:num.
        i < result
        ==> ~(LinearSearch_getDefault a i = e))`;;

let LinearSearch_spec_satisfied =
  `!a:int list. !e:int.
     LinearSearch_precond a e
     ==> LinearSearch_postcond a e (LinearSearch a e)`;;
