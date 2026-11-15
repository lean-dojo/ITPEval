(*
  Statement-only formalization of VERINA corpus artifact verina_basic_17,
  catalog title "toLowercase": an executable Unicode-string map converts each
  uppercase ASCII letter to its lowercase counterpart and leaves every other
  character unchanged, with its total correctness contract. This file contains
  no proof.
*)

let toLowercase_validChar = new_definition
  `toLowercase_validChar (c:num) <=>
     c < 55296 \/ (57343 < c /\ c < 1114112)`;;

let toLowercase_string = new_definition
  `toLowercase_string (s:num list) <=>
     ALL toLowercase_validChar s`;;

let isUpperCase = new_definition
  `isUpperCase (c:num) <=> 65 <= c /\ c <= 90`;;

let shift32 = new_definition
  `shift32 (c:num) =
     if toLowercase_validChar (c + 32) then c + 32 else 0`;;

let toLowercase_precond = new_definition
  `toLowercase_precond (s:num list) <=> T`;;

let toLowercase = new_definition
  `toLowercase (s:num list) =
     MAP
       (\c:num. if isUpperCase c then shift32 c else c)
       s`;;

let toLowercase_postcond = new_definition
  `toLowercase_postcond
      (s:num list) (result:num list) <=>
     LENGTH result = LENGTH s /\
     (!i:num.
        i < LENGTH s
        ==> (isUpperCase (EL i s)
             ==> EL i result = shift32 (EL i s)) /\
            (~isUpperCase (EL i s)
             ==> EL i result = EL i s))`;;

let toLowercase_spec_satisfied =
  `!s:num list.
     toLowercase_string s
     ==> toLowercase_precond s
     ==> toLowercase_postcond s (toLowercase s)`;;
