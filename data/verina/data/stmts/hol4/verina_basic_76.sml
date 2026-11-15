(*
  Statement-only formalization of VERINA corpus artifact verina_basic_76,
  catalog title "myMin": the total executable integer program computes the
  minimum of two inputs by selecting x when x is strictly less than y and y
  otherwise, under its unrestricted precondition and two-branch correctness
  contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

val myMin_precond_def = new_definition (
  "myMin_precond_def",
  ``myMin_precond (x : int) (y : int) <=> T``
);

val myMin_def = new_definition (
  "myMin_def",
  ``myMin (x : int) (y : int) =
      if x < y then x else y``
);

val myMin_postcond_def = new_definition (
  "myMin_postcond_def",
  ``myMin_postcond (x : int) (y : int) (result : int) <=>
      (x <= y ==> result = x) /\
      (x > y ==> result = y)``
);

val myMin_spec_satisfied =
  ``!(x : int) (y : int).
      myMin_precond x y ==>
      myMin_postcond x y (myMin x y)``;
