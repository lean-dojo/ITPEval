(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_65,
  catalog title "reverseString": an executable tail-recursive accumulator
  reverses the character list of a Unicode string, with its total precondition
  and exact length-and-reversal postcondition. This file contains no proof.
*)

let reverseString_validChar = new_definition
  `reverseString_validChar (c:num) <=>
     c < 55296 \/ (57343 < c /\ c < 1114112)`;;

let reverseString_string = new_definition
  `reverseString_string (s:num list) <=>
     ALL reverseString_validChar s`;;

let reverseString_precond = new_definition
  `reverseString_precond (s:num list) <=> T`;;

let reverseString_reverseAux =
  new_recursive_definition list_RECURSION
    `(!acc:num list.
        reverseString_reverseAux ([]:num list) acc = acc) /\
     (!h:num. !t:num list. !acc:num list.
        reverseString_reverseAux (CONS h t) acc =
        reverseString_reverseAux t (CONS h acc))`;;

let reverseString = new_definition
  `reverseString (s:num list) =
     reverseString_reverseAux s []`;;

let reverseString_postcond = new_definition
  `reverseString_postcond
      (s:num list) (result:num list) <=>
     LENGTH result = LENGTH s /\
     result = REVERSE s`;;

let reverseString_spec_satisfied =
  `!s:num list.
     reverseString_string s
     ==> reverseString_precond s
     ==> reverseString_postcond s (reverseString s)`;;
