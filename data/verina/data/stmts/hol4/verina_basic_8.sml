(*
  Statement-only formalization of VERINA corpus artifact verina_basic_8,
  catalog title "myMin": the total executable integer program returns the
  minimum of two inputs by selecting a when a is less than or equal to b and
  b otherwise, under its unrestricted precondition and minimum correctness
  contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

val myMin_precond_def = new_definition (
  "myMin_precond_def",
  ``myMin_precond (a : int) (b : int) <=> T``
);

val myMin_def = new_definition (
  "myMin_def",
  ``myMin (a : int) (b : int) =
      if a <= b then a else b``
);

val myMin_postcond_def = new_definition (
  "myMin_postcond_def",
  ``myMin_postcond (a : int) (b : int) (result : int) <=>
      (result <= a /\ result <= b) /\
      (result = a \/ result = b)``
);

val myMin_spec_satisfied =
  ``!(a : int) (b : int).
      myMin_precond a b ==>
      myMin_postcond a b (myMin a b)``;
