(*
  Statement-only formalization of VERINA corpus artifact verina_basic_19,
  catalog title "isSorted": the executable Boolean program checks every
  adjacent pair of an integer array for non-decreasing order, together with
  its unconditional correctness contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory rich_listTheory;

val isSorted_precond_def = new_definition (
  "isSorted_precond_def",
  ``isSorted_precond (a : int list) <=> T``
);

val isSorted_indexCheck_def = new_definition (
  "isSorted_indexCheck_def",
  ``isSorted_indexCheck (a : int list) (i : num) =
      if i + 1 < LENGTH a then
        EL i a <= EL (i + 1) a
      else
        T``
);

val isSorted_def = new_definition (
  "isSorted_def",
  ``isSorted (a : int list) =
      if LENGTH a <= 1 then
        T
      else
        EVERY
          (isSorted_indexCheck a)
          (COUNT_LIST (LENGTH a))``
);

val isSorted_postcond_def = new_definition (
  "isSorted_postcond_def",
  ``isSorted_postcond (a : int list) (result : bool) <=>
      ((!i : num.
          i < LENGTH a - 1 ==>
          EL i a <= EL (i + 1) a) <=>
       result)``
);

val isSorted_spec_satisfied =
  ``!a : int list.
      isSorted_precond a ==>
      isSorted_postcond a (isSorted a)``;
