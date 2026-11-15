(*
  Statement-only formalization of VERINA corpus artifact verina_basic_75
  (verina__hol-light__verina_basic_75), catalog title "minArray": an executable
  left-to-right scan of a nonempty integer array returns an array element that
  is less than or equal to every element. This file contains no proof.
*)

let minArray_getDefault = new_definition
  `minArray_getDefault (a:int list) (i:num) =
     if i < LENGTH a then EL i a else (&0:int)`;;

let minArray_precond = new_definition
  `minArray_precond (a:int list) <=>
     0 < LENGTH a`;;

let minArray_loopFuel =
  new_recursive_definition num_RECURSION
    `(!a:int list. !i:num. !currentMin:int.
        minArray_loopFuel 0 a i currentMin = currentMin) /\
     (!fuel:num. !a:int list. !i:num. !currentMin:int.
        minArray_loopFuel (SUC fuel) a i currentMin =
        if i < LENGTH a then
          let newMin =
            if currentMin > minArray_getDefault a i then
              minArray_getDefault a i
            else
              currentMin in
          minArray_loopFuel fuel a (i + 1) newMin
        else
          currentMin)`;;

let minArray_loop = new_definition
  `minArray_loop (a:int list) (i:num) (currentMin:int) =
     minArray_loopFuel (LENGTH a - i) a i currentMin`;;

let minArray = new_definition
  `minArray (a:int list) =
     minArray_loop a 1 (minArray_getDefault a 0)`;;

let minArray_postcond = new_definition
  `minArray_postcond (a:int list) (result:int) <=>
     (!i:num.
        i < LENGTH a
        ==> result <= minArray_getDefault a i) /\
     (?i:num.
        i < LENGTH a /\
        result = minArray_getDefault a i)`;;

let minArray_spec_satisfied =
  `!a:int list.
     minArray_precond a
     ==> minArray_postcond a (minArray a)`;;
