(*
  Statement-only formalization of VERINA corpus artifact verina_basic_74
  (verina__hol-light__verina_basic_74), catalog title "maxArray": an executable
  left-to-right scan of a nonempty integer array returns an array element that
  is greater than or equal to every element. This file contains no proof.
*)

let maxArray_getDefault = new_definition
  `maxArray_getDefault (a:int list) (index:num) =
     if index < LENGTH a then EL index a else (&0:int)`;;

let maxArray_precond = new_definition
  `maxArray_precond (a:int list) <=>
     0 < LENGTH a`;;

let maxArray_auxFuel =
  new_recursive_definition num_RECURSION
    `(!a:int list. !index:num. !current:int.
        maxArray_auxFuel 0 a index current = current) /\
     (!fuel:num. !a:int list. !index:num. !current:int.
        maxArray_auxFuel (SUC fuel) a index current =
        if index < LENGTH a then
          let new_current =
            if current > maxArray_getDefault a index then
              current
            else
              maxArray_getDefault a index in
          maxArray_auxFuel fuel a (index + 1) new_current
        else
          current)`;;

let maxArray_aux = new_definition
  `maxArray_aux (a:int list) (index:num) (current:int) =
     maxArray_auxFuel (LENGTH a - index) a index current`;;

let maxArray = new_definition
  `maxArray (a:int list) =
     maxArray_aux a 1 (maxArray_getDefault a 0)`;;

let maxArray_postcond = new_definition
  `maxArray_postcond (a:int list) (result:int) <=>
     (!k:num.
        k < LENGTH a
        ==> maxArray_getDefault a k <= result) /\
     (?k:num.
        k < LENGTH a /\
        result = maxArray_getDefault a k)`;;

let maxArray_spec_satisfied =
  `!a:int list.
     maxArray_precond a
     ==> maxArray_postcond a (maxArray a)`;;
