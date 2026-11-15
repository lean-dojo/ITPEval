(*
  Statement-only formalization of VERINA corpus artifact verina_basic_86
  (verina__hol-light__verina_basic_86), catalog title "rotate": an executable
  left rotation of an integer array by a nonnegative integer offset, using
  Euclidean modular indexing and indexed updates, together with its exact
  length-and-pointwise correctness contract. This file contains no proof.
*)

let rotate_precond = new_definition
  `rotate_precond (a:int list) (offset:int) <=>
     (&0:int) <= offset`;;

let rotate_getDefault = new_definition
  `rotate_getDefault (a:int list) (i:num) =
     if i < LENGTH a then EL i a else (&0:int)`;;

let rotate_setAt =
  new_recursive_definition list_RECURSION
    `(!i:num. !value:int.
        rotate_setAt ([]:int list) i value = []) /\
     (!x:int. !xs:int list. !i:num. !value:int.
        rotate_setAt (CONS x xs) i value =
        if i = 0 then CONS value xs
        else CONS x (rotate_setAt xs (PRE i) value))`;;

let rotate_intToNat = new_definition
  `rotate_intToNat (z:int) =
     if z < (&0:int) then 0 else num_of_int z`;;

let rotateAuxFuel =
  new_recursive_definition num_RECURSION
    `(!a:int list. !offset:int. !i:num. !len:num. !b:int list.
        rotateAuxFuel 0 a offset i len b = b) /\
     (!fuel:num. !a:int list. !offset:int. !i:num. !len:num.
      !b:int list.
        rotateAuxFuel (SUC fuel) a offset i len b =
        if i < len then
          let idx_int =
            ((&i:int) + offset) rem (&len:int) in
          let idx_int_adjusted =
            if idx_int < (&0:int) then idx_int + (&len:int)
            else idx_int in
          let idx_nat = rotate_intToNat idx_int_adjusted in
          let new_b =
            rotate_setAt b i (rotate_getDefault a idx_nat) in
          rotateAuxFuel fuel a offset (i + 1) len new_b
        else
          b)`;;

let rotateAux = new_definition
  `rotateAux
      (a:int list) (offset:int) (i:num) (len:num) (b:int list) =
     rotateAuxFuel (len - i) a offset i len b`;;

let rotate = new_definition
  `rotate (a:int list) (offset:int) =
     let len = LENGTH a in
     let default_val =
       if len > 0 then rotate_getDefault a 0 else (&0:int) in
     let b0 = REPLICATE len default_val in
     rotateAux a offset 0 len b0`;;

let rotate_postcond = new_definition
  `rotate_postcond
      (a:int list) (offset:int) (result:int list) <=>
     LENGTH result = LENGTH a /\
     (!i:num.
        i < LENGTH a
        ==> rotate_getDefault result i =
            rotate_getDefault a
              (rotate_intToNat
                (((&i:int) + offset) rem (&(LENGTH a):int))))`;;

let rotate_spec_satisfied =
  `!a:int list. !offset:int.
     rotate_precond a offset
     ==> rotate_postcond a offset (rotate a offset)`;;
