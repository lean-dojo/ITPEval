(*
  Statement-only formalization of VERINA corpus artifact verina_basic_2,
  catalog title "findSmallest": the executable optional-minimum program
  returns NONE exactly for an empty natural-number array and otherwise returns
  an attained least element. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory optionTheory;

val findSmallest_min_def = new_definition (
  "findSmallest_min_def",
  ``findSmallest_min (a : num) (b : num) =
      if a <= b then a else b``
);

val findSmallest_precond_def = new_definition (
  "findSmallest_precond_def",
  ``findSmallest_precond (s : num list) <=> T``
);

val findSmallest_def = new_definition (
  "findSmallest_def",
  ``findSmallest (s : num list) =
      case s of
        [] => (NONE : num option)
      | x::xs => SOME (FOLDL findSmallest_min x xs)``
);

val findSmallest_postcond_def = new_definition (
  "findSmallest_postcond_def",
  ``findSmallest_postcond
      (s : num list) (result : num option) <=>
      case result of
        NONE => s = []
      | SOME r =>
          MEM r s /\
          (!x : num. MEM x s ==> r <= x)``
);

val findSmallest_spec_satisfied =
  ``!s : num list.
      findSmallest_precond s ==>
      findSmallest_postcond s (findSmallest s)``;
