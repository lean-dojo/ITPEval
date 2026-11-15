(*
  Statement-only formalization of VERINA corpus artifact verina_basic_18,
  catalog title "sumOfDigits": the executable natural-number program
  repeatedly takes base-10 remainders and quotients to sum the decimal digits,
  with its precondition and decimal-representation postcondition. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory;

val sumOfDigits_loopFuel_def = Define `
  (sumOfDigits_loopFuel
      0 (n : num) (acc : num) =
     acc) /\
  (sumOfDigits_loopFuel
      (SUC fuel) n acc =
     if n = 0 then
       acc
     else
       sumOfDigits_loopFuel fuel (n DIV 10) (acc + n MOD 10))
`;

val sumOfDigits_precond_def = new_definition (
  "sumOfDigits_precond_def",
  ``sumOfDigits_precond (n : num) <=> T``
);

val sumOfDigits_def = new_definition (
  "sumOfDigits_def",
  ``sumOfDigits (n : num) =
      sumOfDigits_loopFuel n n 0``
);

val sumOfDigits_decimalDigitsFuel_def = Define `
  (sumOfDigits_decimalDigitsFuel
      0 (n : num) =
     ([] : num list)) /\
  (sumOfDigits_decimalDigitsFuel
      (SUC fuel) n =
     if n < 10 then
       [n]
     else
       sumOfDigits_decimalDigitsFuel fuel (n DIV 10) ++ [n MOD 10])
`;

val sumOfDigits_decimalDigits_def = new_definition (
  "sumOfDigits_decimalDigits_def",
  ``sumOfDigits_decimalDigits (n : num) =
      if n = 0 then
        [0]
      else
        sumOfDigits_decimalDigitsFuel n n``
);

val sumOfDigits_postcond_def = new_definition (
  "sumOfDigits_postcond_def",
  ``sumOfDigits_postcond (n : num) (result : num) <=>
      let digitSum =
        FOLDL
          (\acc d. acc + d)
          0
          (sumOfDigits_decimalDigits n)
      in
        result - digitSum = 0 /\
        digitSum - result = 0``
);

val sumOfDigits_spec_satisfied =
  ``!n : num.
      sumOfDigits_precond n ==>
      sumOfDigits_postcond n (sumOfDigits n)``;
