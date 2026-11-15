(*
  Statement-only formalization of VERINA corpus artifact verina_basic_11,
  catalog title "lastDigit": an executable natural-number remainder
  computation returns the last decimal digit, together with its total
  precondition and range-and-equality correctness contract. This file contains
  no proof.
*)

let lastDigit_precond = new_definition
  `lastDigit_precond (n:num) <=> T`;;

let lastDigit = new_definition
  `lastDigit (n:num) = n MOD 10`;;

let lastDigit_postcond = new_definition
  `lastDigit_postcond (n:num) (result:num) <=>
     (0 <= result /\ result < 10) /\
     (n MOD 10 - result = 0 /\ result - n MOD 10 = 0)`;;

let lastDigit_spec_satisfied =
  `!n:num.
     lastDigit_precond n
     ==> lastDigit_postcond n (lastDigit n)`;;
