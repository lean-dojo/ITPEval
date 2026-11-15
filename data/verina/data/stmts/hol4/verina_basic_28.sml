(*
  Statement-only formalization of VERINA corpus artifact verina_basic_28,
  catalog title "isPrime": the fuel-bounded executable Boolean program tests
  divisibility from two upward, under the n >= 2 precondition, and satisfies
  its all-divisors/two-direction postcondition. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory;

val isPrime_precond_def = new_definition (
  "isPrime_precond_def",
  ``isPrime_precond (n : num) <=> n >= 2``
);

val isPrime_check_def = Define `
  (isPrime_check
      (n : num) (i : num) 0 =
     T) /\
  (isPrime_check
      n i (SUC fuel) =
     if i * i > n then
       T
     else if n MOD i = 0 then
       F
     else
       isPrime_check n (i + 1) fuel)
`;

val isPrime_def = new_definition (
  "isPrime_def",
  ``isPrime (n : num) =
      isPrime_check n 2 n``
);

val isPrime_candidates_def = new_definition (
  "isPrime_candidates_def",
  ``isPrime_candidates (n : num) =
      GENLIST (\offset : num. 2 + offset) (n - 2)``
);

val isPrime_postcond_def = new_definition (
  "isPrime_postcond_def",
  ``isPrime_postcond (n : num) (result : bool) <=>
      (result ==>
       EVERY
         (\k : num. n MOD k <> 0)
         (isPrime_candidates n)) /\
      (~result ==>
       EXISTS
         (\k : num. n MOD k = 0)
         (isPrime_candidates n))``
);

val isPrime_spec_satisfied =
  ``!n : num.
      isPrime_precond n ==>
      isPrime_postcond n (isPrime n)``;
