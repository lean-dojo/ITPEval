(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_72,
  catalog title "singleDigitPrimeFactor": the executable decision tree returns
  the smallest prime factor among 2, 3, 5, and 7 for a natural number, or 0
  when the input is 0 or none of those primes divides it, and satisfies the
  stated bounded-factor contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory;

val singleDigitPrimeFactor_precond_def = new_definition (
  "singleDigitPrimeFactor_precond_def",
  ``singleDigitPrimeFactor_precond (n : num) <=> T``
);

val singleDigitPrimeFactor_def = new_definition (
  "singleDigitPrimeFactor_def",
  ``singleDigitPrimeFactor (n : num) =
      if n = 0 then
        0
      else if n MOD 2 = 0 then
        2
      else if n MOD 3 = 0 then
        3
      else if n MOD 5 = 0 then
        5
      else if n MOD 7 = 0 then
        7
      else
        0``
);

val singleDigitPrimeFactor_postcond_def = new_definition (
  "singleDigitPrimeFactor_postcond_def",
  ``singleDigitPrimeFactor_postcond
      (n : num) (result : num) <=>
      MEM result [0; 2; 3; 5; 7] /\
      (result = 0 ==>
       (n = 0 \/
        EVERY
          (\p : num. n MOD p <> 0)
          [2; 3; 5; 7])) /\
      (result <> 0 ==>
       n <> 0 /\
       n MOD result = 0 /\
       EVERY
         (\x : num.
           MEM x [2; 3; 5; 7] ==>
           n MOD x <> 0)
         (COUNT_LIST result))``
);

val singleDigitPrimeFactor_spec_satisfied =
  ``!n : num.
      singleDigitPrimeFactor_precond n ==>
      singleDigitPrimeFactor_postcond
        n (singleDigitPrimeFactor n)``;
