(*
  Statement-only formalization of VERINA corpus artifact verina_basic_42
  (verina__hol-light__verina_basic_42), catalog title "countDigits": an
  executable Unicode-string computation counts exactly the characters from
  '0' through '9', together with its total precondition and truncated-natural
  subtraction correctness contract. This file contains no proof.
*)

let countDigits_validChar = new_definition
  `countDigits_validChar (c:num) <=>
     c < 55296 \/ (57343 < c /\ c < 1114112)`;;

let countDigits_string = new_definition
  `countDigits_string (s:num list) <=>
     ALL countDigits_validChar s`;;

let isDigit = new_definition
  `isDigit (c:num) <=>
     48 <= c /\ c <= 57`;;

let countDigits_precond = new_definition
  `countDigits_precond (s:num list) <=> T`;;

let countDigits = new_definition
  `countDigits (s:num list) =
     LENGTH (FILTER isDigit s)`;;

let countDigits_postcond = new_definition
  `countDigits_postcond
      (s:num list) (result:num) <=>
     result - LENGTH (FILTER isDigit s) = 0 /\
     LENGTH (FILTER isDigit s) - result = 0`;;

let countDigits_spec_satisfied =
  `!s:num list.
     countDigits_string s
     ==> countDigits_precond s
     ==> countDigits_postcond s (countDigits s)`;;
