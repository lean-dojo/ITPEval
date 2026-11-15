(*
  Statement-only formalization of VERINA corpus artifact verina_basic_82
  (verina__hol-light__verina_basic_82), catalog title "remove_front": an
  executable copy loop removes the first element of a nonempty integer array,
  with the exact shifted-element and length correctness contract. This file
  contains no proof.
*)

let remove_front_precond = new_definition
  `remove_front_precond (a:int list) <=>
     LENGTH a > 0`;;

let remove_front_getDefault = new_definition
  `remove_front_getDefault (a:int list) (i:num) =
     if i < LENGTH a then EL i a else (&0:int)`;;

let copyFromFuel =
  new_recursive_definition num_RECURSION
    `(!a:int list. !i:num. !acc:int list.
        copyFromFuel 0 a i acc = acc) /\
     (!fuel:num. !a:int list. !i:num. !acc:int list.
        copyFromFuel (SUC fuel) a i acc =
        if i < LENGTH a then
          copyFromFuel fuel a (i + 1)
            (APPEND acc
              (CONS (remove_front_getDefault a i) []))
        else
          acc)`;;

let copyFrom = new_definition
  `copyFrom (a:int list) (i:num) (acc:int list) =
     copyFromFuel (LENGTH a - i) a i acc`;;

let remove_front = new_definition
  `remove_front (a:int list) =
     if LENGTH a > 0 then
       copyFrom a 1 ([]:int list)
     else
       []`;;

let remove_front_postcond = new_definition
  `remove_front_postcond
      (a:int list) (result:int list) <=>
     LENGTH a > 0 /\
     LENGTH result = LENGTH a - 1 /\
     (!i:num.
        i < LENGTH result
        ==> remove_front_getDefault result i =
            remove_front_getDefault a (i + 1))`;;

let remove_front_spec_satisfied =
  `!a:int list.
     remove_front_precond a
     ==> remove_front_postcond
           a (remove_front a)`;;
