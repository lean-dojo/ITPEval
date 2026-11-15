(*
  Statement-only formalization of VERINA corpus artifact verina_basic_3,
  catalog title "isDivisibleBy11": the executable integer test returns true
  exactly when the input is divisible by 11 and satisfies its two-direction
  divisibility correctness contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

val isDivisibleBy11_precond_def = new_definition (
  "isDivisibleBy11_precond_def",
  ``isDivisibleBy11_precond (n : int) <=> T``
);

val isDivisibleBy11_def = new_definition (
  "isDivisibleBy11_def",
  ``isDivisibleBy11 (n : int) = (n % 11 = 0)``
);

val isDivisibleBy11_postcond_def = new_definition (
  "isDivisibleBy11_postcond_def",
  ``isDivisibleBy11_postcond (n : int) (result : bool) <=>
      (result ==> ?k : int. n = 11 * k) /\
      (~result ==> !k : int. n <> 11 * k)``
);

val isDivisibleBy11_spec_satisfied =
  ``!n : int.
      isDivisibleBy11_precond n ==>
      isDivisibleBy11_postcond n (isDivisibleBy11 n)``;
