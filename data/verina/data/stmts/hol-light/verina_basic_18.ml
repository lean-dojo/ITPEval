(*
  Statement-only formalization of VERINA corpus artifact verina_basic_18,
  catalog title "sumOfDigits": an executable decimal-digit loop computes the
  sum of the digits of any natural number, with its total precondition and
  decimal-representation correctness contract. This file contains no proof.
*)

let sumOfDigits_precond = new_definition
  `sumOfDigits_precond (n:num) <=> T`;;

let sumOfDigits_loopFuel =
  new_recursive_definition num_RECURSION
    `(!n:num. !acc:num.
        sumOfDigits_loopFuel 0 n acc = acc) /\
     (!fuel:num. !n:num. !acc:num.
        sumOfDigits_loopFuel (SUC fuel) n acc =
        if n = 0 then acc
        else
          sumOfDigits_loopFuel
            fuel (n DIV 10) (acc + n MOD 10))`;;

let sumOfDigits = new_definition
  `sumOfDigits (n:num) =
     sumOfDigits_loopFuel (SUC n) n 0`;;

let sumOfDigits_decimalDigitsFuel =
  new_recursive_definition num_RECURSION
    `(!n:num.
        sumOfDigits_decimalDigitsFuel 0 n = []) /\
     (!fuel:num. !n:num.
        sumOfDigits_decimalDigitsFuel (SUC fuel) n =
        if n < 10 then CONS n []
        else
          APPEND
            (sumOfDigits_decimalDigitsFuel fuel (n DIV 10))
            (CONS (n MOD 10) []))`;;

let sumOfDigits_decimalDigits = new_definition
  `sumOfDigits_decimalDigits (n:num) =
     if n = 0 then CONS 0 []
     else sumOfDigits_decimalDigitsFuel n n`;;

let sumOfDigits_listSum =
  new_recursive_definition list_RECURSION
    `(sumOfDigits_listSum ([]:num list) = 0) /\
     (!d:num. !ds:num list.
        sumOfDigits_listSum (CONS d ds) =
        d + sumOfDigits_listSum ds)`;;

let sumOfDigits_postcond = new_definition
  `sumOfDigits_postcond (n:num) (result:num) <=>
     let digitSum =
       sumOfDigits_listSum (sumOfDigits_decimalDigits n) in
     result - digitSum = 0 /\
     digitSum - result = 0`;;

let sumOfDigits_spec_satisfied =
  `!n:num.
     sumOfDigits_precond n
     ==> sumOfDigits_postcond n (sumOfDigits n)`;;
