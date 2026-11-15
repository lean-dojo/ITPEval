(*
  Statement-only formalization of VERINA artifact verina_advanced_18,
  cataloged as "isArmstrong": the executable Boolean program tests whether a
  natural number equals the sum of its decimal digits raised to the number of
  decimal digits. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory;

val countDigitsFuel_def = Define `
  (countDigitsFuel 0 (n : num) (acc : num) = acc) /\
  (countDigitsFuel (SUC fuel) n acc =
     if n = 0 then
       acc
     else
       countDigitsFuel fuel (n DIV 10) (acc + 1))
`;

val countDigits_def = new_definition (
  "countDigits_def",
  ``countDigits (n : num) =
      countDigitsFuel n n (if n = 0 then 1 else 0)``
);

val isArmstrong_precond_def = new_definition (
  "isArmstrong_precond_def",
  ``isArmstrong_precond (n : num) <=> T``
);

val sumPowersFuel_def = Define `
  (sumPowersFuel 0 (n : num) (k : num) (acc : num) = acc) /\
  (sumPowersFuel (SUC fuel) n k acc =
     if n = 0 then
       acc
     else
       sumPowersFuel fuel
         (n DIV 10)
         k
         (acc + (n MOD 10) EXP k))
`;

val sumPowers_def = new_definition (
  "sumPowers_def",
  ``sumPowers (n : num) (k : num) =
      sumPowersFuel n n k 0``
);

val isArmstrong_def = new_definition (
  "isArmstrong_def",
  ``isArmstrong (n : num) =
      (sumPowers n (countDigits n) = n)``
);

val decimalDigitsFuel_def = Define `
  (decimalDigitsFuel 0 (n : num) = ([] : num list)) /\
  (decimalDigitsFuel (SUC fuel) n =
     if n < 10 then
       [n]
     else
       decimalDigitsFuel fuel (n DIV 10) ++ [n MOD 10])
`;

val decimalDigits_def = new_definition (
  "decimalDigits_def",
  ``decimalDigits (n : num) =
      if n = 0 then [0] else decimalDigitsFuel n n``
);

val isArmstrong_postcond_def = new_definition (
  "isArmstrong_postcond_def",
  ``isArmstrong_postcond (n : num) (result : bool) <=>
      let n' =
        FOLDL
          (\acc d. acc + d EXP countDigits n)
          0
          (decimalDigits n)
      in
        (result ==> n = n') /\
        (~result ==> n <> n')``
);

val isArmstrong_spec_satisfied =
  ``!n : num.
      isArmstrong_precond n ==>
      isArmstrong_postcond n (isArmstrong n)``;
