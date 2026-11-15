(*
  Statement-only formalization of VERINA corpus artifact verina_basic_61
  (verina__hol-light__verina_basic_61), catalog title "allDigits": an
  executable Unicode-string scan returns true exactly when every character is
  an ASCII decimal digit, together with its total precondition and Boolean
  correctness contract. This file contains no proof.
*)

let allDigits_validChar = new_definition
  `allDigits_validChar (c:num) <=>
     c < 55296 \/ (57343 < c /\ c < 1114112)`;;

let allDigits_string = new_definition
  `allDigits_string (s:num list) <=>
     ALL allDigits_validChar s`;;

let isDigit = new_definition
  `isDigit (c:num) <=>
     48 <= c /\ c <= 57`;;

let allDigits_precond = new_definition
  `allDigits_precond (s:num list) <=> T`;;

let allDigits =
  new_recursive_definition list_RECURSION
    `(allDigits ([]:num list) = T) /\
     (!c:num. !cs:num list.
        allDigits (CONS c cs) =
        if ~isDigit c then F
        else allDigits cs)`;;

let allDigits_postcond = new_definition
  `allDigits_postcond (s:num list) (result:bool) <=>
     (result = T <=> ALL isDigit s)`;;

let allDigits_spec_satisfied =
  `!s:num list.
     allDigits_string s
     ==> allDigits_precond s
     ==> allDigits_postcond s (allDigits s)`;;
