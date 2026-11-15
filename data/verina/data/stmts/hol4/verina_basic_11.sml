(*
  Statement-only formalization of VERINA corpus artifact verina_basic_11,
  catalog title "lastDigit": the executable natural-number program returns
  the remainder modulo 10 and satisfies the last-digit range and equality
  contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory;

val lastDigit_precond_def = new_definition (
  "lastDigit_precond_def",
  ``lastDigit_precond (n : num) <=> T``
);

val lastDigit_def = new_definition (
  "lastDigit_def",
  ``lastDigit (n : num) = (n MOD 10)``
);

val lastDigit_postcond_def = new_definition (
  "lastDigit_postcond_def",
  ``lastDigit_postcond (n : num) (result : num) <=>
      (0 <= result /\ result < 10) /\
      ((n MOD 10) - result = 0 /\ result - (n MOD 10) = 0)``
);

val lastDigit_spec_satisfied =
  ``!n : num.
      lastDigit_precond n ==>
      lastDigit_postcond n (lastDigit n)``;
