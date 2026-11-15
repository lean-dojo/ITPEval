(*
  Statement-only formalization of VERINA corpus artifact verina_basic_31
  (verina__hol-light__verina_basic_31), catalog title "toUppercase": an
  executable Unicode-string map converts each lowercase ASCII letter to its
  uppercase counterpart and leaves every other character unchanged, together
  with its total correctness contract. This file contains no proof.
*)

let toUppercase_validChar = new_definition
  `toUppercase_validChar (c:num) <=>
     c < 55296 \/ (57343 < c /\ c < 1114112)`;;

let toUppercase_string = new_definition
  `toUppercase_string (s:num list) <=>
     ALL toUppercase_validChar s`;;

let isLowerCase = new_definition
  `isLowerCase (c:num) <=> 97 <= c /\ c <= 122`;;

let shiftMinus32 = new_definition
  `shiftMinus32 (c:num) = (c - 32) MOD 128`;;

let toUppercase_precond = new_definition
  `toUppercase_precond (s:num list) <=> T`;;

let toUppercase = new_definition
  `toUppercase (s:num list) =
     MAP
       (\c:num. if isLowerCase c then shiftMinus32 c else c)
       s`;;

let toUppercase_postcond = new_definition
  `toUppercase_postcond
      (s:num list) (result:num list) <=>
     LENGTH result = LENGTH s /\
     (!i:num.
        i < LENGTH s
        ==> (isLowerCase (EL i s)
             ==> EL i result = shiftMinus32 (EL i s)) /\
            (~isLowerCase (EL i s)
             ==> EL i result = EL i s))`;;

let toUppercase_spec_satisfied =
  `!s:num list.
     toUppercase_string s
     ==> toUppercase_precond s
     ==> toUppercase_postcond s (toUppercase s)`;;
