(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_18,
  catalog title "isArmstrong": an executable decimal-digit computation tests
  whether a natural number equals the sum of its digits raised to the number
  of digits, together with its total correctness contract. This file contains
  no proof.
*)

let countDigits_go = define
  `countDigits_go(n,acc) =
     if n = 0 then acc
     else countDigits_go(n DIV 10,acc + 1)`;;

let countDigits = new_definition
  `countDigits (n:num) =
     countDigits_go(n,if n = 0 then 1 else 0)`;;

let isArmstrong_precond = new_definition
  `isArmstrong_precond (n:num) <=> T`;;

let sumPowers_go = define
  `sumPowers_go(n,k,acc) =
     if n = 0 then acc
     else
       let digit = n MOD 10 in
       sumPowers_go(n DIV 10,k,acc + digit EXP k)`;;

let sumPowers = new_definition
  `sumPowers (n:num) (k:num) = sumPowers_go(n,k,0)`;;

let isArmstrong = new_definition
  `isArmstrong (n:num) =
     (sumPowers n (countDigits n) = n)`;;

let isArmstrong_decimalDigits = define
  `isArmstrong_decimalDigits (n:num) =
     if n < 10 then CONS n []
     else
       APPEND
         (isArmstrong_decimalDigits (n DIV 10))
         (CONS (n MOD 10) [])`;;

let isArmstrong_foldDigitPowers =
  new_recursive_definition list_RECURSION
    `(!k:num. !acc:num.
        isArmstrong_foldDigitPowers k acc [] = acc) /\
     (!d:num. !ds:num list. !k:num. !acc:num.
        isArmstrong_foldDigitPowers k acc (CONS d ds) =
        isArmstrong_foldDigitPowers
          k (acc + d EXP k) ds)`;;

let isArmstrong_postcond = new_definition
  `isArmstrong_postcond
      (n:num) (result:bool) <=>
     let n' =
       isArmstrong_foldDigitPowers
         (countDigits n) 0 (isArmstrong_decimalDigits n) in
     (result ==> n = n') /\
     (~result ==> ~(n = n'))`;;

let isArmstrong_spec_satisfied =
  `!n:num.
     isArmstrong_precond n
     ==> isArmstrong_postcond n (isArmstrong n)`;;
