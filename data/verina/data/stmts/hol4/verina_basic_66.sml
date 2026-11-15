(*
  Statement-only formalization of VERINA corpus artifact verina_basic_66,
  catalog title "ComputeIsEven": the executable Boolean program tests whether
  an arbitrary integer has zero remainder modulo two, and its correctness
  contract characterizes even integers as integer multiples of two. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

val ComputeIsEven_precond_def = new_definition (
  "ComputeIsEven_precond_def",
  ``ComputeIsEven_precond (x : int) <=> T``
);

val ComputeIsEven_def = new_definition (
  "ComputeIsEven_def",
  ``ComputeIsEven (x : int) =
      if x % 2 = 0 then T else F``
);

val ComputeIsEven_postcond_def = new_definition (
  "ComputeIsEven_postcond_def",
  ``ComputeIsEven_postcond (x : int) (result : bool) <=>
      (result = T <=> ?k : int. x = 2 * k)``
);

val ComputeIsEven_spec_satisfied =
  ``!x : int.
      ComputeIsEven_precond x ==>
      ComputeIsEven_postcond x (ComputeIsEven x)``;
