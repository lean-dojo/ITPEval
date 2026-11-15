(*
  Statement-only formalization of VERINA corpus artifact verina_basic_83
  (verina__hol-light__verina_basic_83), catalog title "concat": an executable
  indexed-update loop concatenates two arbitrary integer arrays, together with
  its total precondition and exact length and pointwise correctness contract.
  This file contains no proof.
*)

let concat_precond = new_definition
  `concat_precond (a:int list) (b:int list) <=> T`;;

let concat_getDefault = new_definition
  `concat_getDefault (xs:int list) (i:num) =
     if i < LENGTH xs then EL i xs else (&0:int)`;;

let concat_setAt =
  new_recursive_definition list_RECURSION
    `(!i:num. !value:int.
        concat_setAt ([]:int list) i value = []) /\
     (!x:int. !xs:int list. !i:num. !value:int.
        concat_setAt (CONS x xs) i value =
        if i = 0 then CONS value xs
        else CONS x (concat_setAt xs (PRE i) value))`;;

let concat_loopFuel =
  new_recursive_definition num_RECURSION
    `(!a:int list. !b:int list. !n:num. !i:num. !c:int list.
        concat_loopFuel 0 a b n i c = c) /\
     (!fuel:num. !a:int list. !b:int list. !n:num. !i:num.
      !c:int list.
        concat_loopFuel (SUC fuel) a b n i c =
        if i < n then
          let value =
            if i < LENGTH a then
              concat_getDefault a i
            else
              concat_getDefault b (i - LENGTH a) in
          concat_loopFuel fuel a b n (i + 1)
            (concat_setAt c i value)
        else
          c)`;;

let concat_loop = new_definition
  `concat_loop
      (a:int list) (b:int list) (n:num)
      (i:num) (c:int list) =
     concat_loopFuel (n - i) a b n i c`;;

let concat = new_definition
  `concat (a:int list) (b:int list) =
     let n = LENGTH a + LENGTH b in
     concat_loop a b n 0 (REPLICATE n (&0:int))`;;

let concat_postcond = new_definition
  `concat_postcond
      (a:int list) (b:int list) (result:int list) <=>
     LENGTH result = LENGTH a + LENGTH b /\
     (!k:num.
        k < LENGTH a
        ==> concat_getDefault result k =
            concat_getDefault a k) /\
     (!k:num.
        k < LENGTH b
        ==> concat_getDefault result (k + LENGTH a) =
            concat_getDefault b k)`;;

let concat_spec_satisfied =
  `!a:int list. !b:int list.
     concat_precond a b
     ==> concat_postcond a b (concat a b)`;;
