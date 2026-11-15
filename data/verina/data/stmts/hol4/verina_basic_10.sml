(*
  Statement-only formalization of VERINA corpus artifact verina_basic_10,
  catalog title "isGreater": the executable Boolean test checks whether an
  integer is strictly greater than every element of a nonempty integer array,
  together with its correctness contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val isGreater_precond_def = new_definition (
  "isGreater_precond_def",
  ``isGreater_precond (n : int) (a : int list) <=>
      0 < LENGTH a``
);

val isGreater_def = new_definition (
  "isGreater_def",
  ``isGreater (n : int) (a : int list) =
      EVERY (\x : int. n > x) a``
);

val isGreater_postcond_def = new_definition (
  "isGreater_postcond_def",
  ``isGreater_postcond
      (n : int) (a : int list) (result : bool) <=>
      ((!i : num. i < LENGTH a ==> n > EL i a) <=> result)``
);

val isGreater_spec_satisfied =
  ``!(n : int) (a : int list).
      isGreater_precond n a ==>
      isGreater_postcond n a (isGreater n a)``;
