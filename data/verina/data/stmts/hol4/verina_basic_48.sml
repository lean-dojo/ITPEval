(*
  Statement-only formalization of VERINA corpus artifact verina_basic_48,
  catalog title "isPerfectSquare": the executable fuel-bounded Boolean search
  determines whether a natural number has a natural-number square root and
  satisfies that exact perfect-square postcondition. This file contains no
  proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory;

val isPerfectSquare_precond_def = new_definition (
  "isPerfectSquare_precond_def",
  ``isPerfectSquare_precond (n : num) <=> T``
);

val isPerfectSquare_check_def = Define `
  (isPerfectSquare_check
      (n : num) (x : num) 0 =
     F) /\
  (isPerfectSquare_check
      n x (SUC fuel) =
     if x * x > n then
       F
     else if x * x = n then
       T
     else
       isPerfectSquare_check n (x + 1) fuel)
`;

val isPerfectSquare_def = new_definition (
  "isPerfectSquare_def",
  ``isPerfectSquare (n : num) =
      if n = 0 then
        T
      else
        isPerfectSquare_check n 1 n``
);

val isPerfectSquare_postcond_def = new_definition (
  "isPerfectSquare_postcond_def",
  ``isPerfectSquare_postcond
      (n : num) (result : bool) <=>
      (result <=> ?i : num. i * i = n)``
);

val isPerfectSquare_spec_satisfied =
  ``!n : num.
      isPerfectSquare_precond n ==>
      isPerfectSquare_postcond
        n (isPerfectSquare n)``;
