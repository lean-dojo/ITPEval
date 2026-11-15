(*
  Statement-only formalization of VERINA corpus artifact verina_basic_103,
  catalog title "UpdateElements": the executable integer-array program
  increments index 4 by 3, sets index 7 to 516, and preserves every other
  element. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val UpdateElements_precond_def = new_definition (
  "UpdateElements_precond_def",
  ``UpdateElements_precond (a : int list) <=>
      LENGTH a >= 8``
);

val UpdateElements_def = new_definition (
  "UpdateElements_def",
  ``UpdateElements (a : int list) =
      let a1 = LUPDATE (EL 4 a + 3) 4 a in
        LUPDATE 516 7 a1``
);

val UpdateElements_postcond_def = new_definition (
  "UpdateElements_postcond_def",
  ``UpdateElements_postcond
      (a : int list) (result : int list) <=>
      LENGTH result = LENGTH a /\
      EL 4 result = EL 4 a + 3 /\
      EL 7 result = 516 /\
      (!i.
         i < LENGTH a /\ i <> 4 /\ i <> 7 ==>
         EL i result = EL i a)``
);

val UpdateElements_spec_satisfied =
  ``!a : int list.
      UpdateElements_precond a ==>
      UpdateElements_postcond a (UpdateElements a)``;
