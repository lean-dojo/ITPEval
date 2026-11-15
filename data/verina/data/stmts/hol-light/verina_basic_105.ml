(*
  Statement-only formalization of VERINA corpus artifact verina_basic_105,
  catalog title "arrayProduct": an executable element-wise product of two
  integer arrays, including defaulted indexing and indexed updates, together
  with its equal-length precondition and pointwise correctness contract. This
  file contains no proof.
*)

let arrayProduct_precond = new_definition
  `arrayProduct_precond (a:int list) (b:int list) <=>
     LENGTH a = LENGTH b`;;

let arrayProduct_getDefault = new_definition
  `arrayProduct_getDefault (xs:int list) (i:num) =
     if i < LENGTH xs then EL i xs else (&0:int)`;;

let arrayProduct_setAt =
  new_recursive_definition list_RECURSION
    `(!i:num. !value:int.
        arrayProduct_setAt ([]:int list) i value = []) /\
     (!x:int. !xs:int list. !i:num. !value:int.
        arrayProduct_setAt (CONS x xs) i value =
        if i = 0 then CONS value xs
        else CONS x (arrayProduct_setAt xs (PRE i) value))`;;

let arrayProduct_loopFuel =
  new_recursive_definition num_RECURSION
    `(!a:int list. !b:int list. !len:num. !i:num. !c:int list.
        arrayProduct_loopFuel 0 a b len i c = c) /\
     (!fuel:num. !a:int list. !b:int list. !len:num. !i:num.
      !c:int list.
        arrayProduct_loopFuel (SUC fuel) a b len i c =
        if i < len then
          let a_val = arrayProduct_getDefault a i in
          let b_val = arrayProduct_getDefault b i in
          let new_c =
            arrayProduct_setAt c i (a_val * b_val) in
          arrayProduct_loopFuel fuel a b len (i + 1) new_c
        else
          c)`;;

let arrayProduct_loop = new_definition
  `arrayProduct_loop
      (a:int list) (b:int list) (len:num)
      (i:num) (c:int list) =
     arrayProduct_loopFuel (len - i) a b len i c`;;

let arrayProduct = new_definition
  `arrayProduct (a:int list) (b:int list) =
     let len = LENGTH a in
     let c = REPLICATE len (&0:int) in
     arrayProduct_loop a b len 0 c`;;

let arrayProduct_postcond = new_definition
  `arrayProduct_postcond
      (a:int list) (b:int list) (result:int list) <=>
     LENGTH result = LENGTH a /\
     (!i:num.
        i < LENGTH a
        ==> EL i a * EL i b = EL i result)`;;

let arrayProduct_spec_satisfied =
  `!a:int list. !b:int list.
     arrayProduct_precond a b
     ==> arrayProduct_postcond
           a b (arrayProduct a b)`;;
