(*
  Statement-only formalization of VERINA corpus artifact verina_basic_97
  (verina__hol-light__verina_basic_97), catalog title "TestArrayElements": an
  executable update sets the element at a valid natural-number index of an
  integer array to 60, preserving the array length and every other element.
  This file contains no proof.
*)

let TestArrayElements_precond = new_definition
  `TestArrayElements_precond (a:int list) (j:num) <=>
     j < LENGTH a`;;

let TestArrayElements_setAt =
  new_recursive_definition list_RECURSION
    `(!j:num. !value:int.
        TestArrayElements_setAt ([]:int list) j value = []) /\
     (!x:int. !xs:int list. !j:num. !value:int.
        TestArrayElements_setAt (CONS x xs) j value =
        if j = 0 then CONS value xs
        else CONS x (TestArrayElements_setAt xs (PRE j) value))`;;

let TestArrayElements = new_definition
  `TestArrayElements (a:int list) (j:num) =
     TestArrayElements_setAt a j (&60:int)`;;

let TestArrayElements_postcond = new_definition
  `TestArrayElements_postcond
      (a:int list) (j:num) (result:int list) <=>
     LENGTH result = LENGTH a /\
     EL j result = (&60:int) /\
     (!k:num.
        k < LENGTH a
        ==> ~(k = j)
        ==> EL k result = EL k a)`;;

let TestArrayElements_spec_satisfied =
  `!a:int list. !j:num.
     TestArrayElements_precond a j
     ==> TestArrayElements_postcond
           a j (TestArrayElements a j)`;;
