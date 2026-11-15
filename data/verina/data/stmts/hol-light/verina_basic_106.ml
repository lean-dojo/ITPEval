(*
  Statement-only formalization of VERINA corpus artifact verina_basic_106,
  catalog title "arraySum": an executable element-wise sum of two integer
  arrays, including its length check, zero initialization, defaulted indexing,
  and indexed-update loop, together with its equal-length precondition and
  pointwise correctness contract. This file contains no proof.
*)

let arraySum_precond = new_definition
  `arraySum_precond (a:int list) (b:int list) <=>
     LENGTH a = LENGTH b`;;

let arraySum_getDefault = new_definition
  `arraySum_getDefault (xs:int list) (i:num) =
     if i < LENGTH xs then EL i xs else (&0:int)`;;

let arraySum_setAt =
  new_recursive_definition list_RECURSION
    `(!i:num. !value:int.
        arraySum_setAt ([]:int list) i value = []) /\
     (!x:int. !xs:int list. !i:num. !value:int.
        arraySum_setAt (CONS x xs) i value =
        if i = 0 then CONS value xs
        else CONS x (arraySum_setAt xs (PRE i) value))`;;

let arraySum_loopFuel =
  new_recursive_definition num_RECURSION
    `(!a:int list. !b:int list. !len:num. !i:num. !c:int list.
        arraySum_loopFuel 0 a b len i c = c) /\
     (!fuel:num. !a:int list. !b:int list. !len:num. !i:num.
      !c:int list.
        arraySum_loopFuel (SUC fuel) a b len i c =
        if i < len then
          let new_c =
            arraySum_setAt c i
              (arraySum_getDefault a i + arraySum_getDefault b i) in
          arraySum_loopFuel fuel a b len (i + 1) new_c
        else
          c)`;;

let arraySum_loop = new_definition
  `arraySum_loop
      (a:int list) (b:int list) (len:num)
      (i:num) (c:int list) =
     arraySum_loopFuel (len - i) a b len i c`;;

let arraySum = new_definition
  `arraySum (a:int list) (b:int list) =
     if ~(LENGTH a = LENGTH b) then
       ([]:int list)
     else
       let len = LENGTH a in
       let c = REPLICATE len (&0:int) in
       arraySum_loop a b len 0 c`;;

let arraySum_postcond = new_definition
  `arraySum_postcond
      (a:int list) (b:int list) (result:int list) <=>
     LENGTH result = LENGTH a /\
     (!i:num.
        i < LENGTH a
        ==> EL i a + EL i b = EL i result)`;;

let arraySum_spec_satisfied =
  `!a:int list. !b:int list.
     arraySum_precond a b
     ==> arraySum_postcond a b (arraySum a b)`;;
