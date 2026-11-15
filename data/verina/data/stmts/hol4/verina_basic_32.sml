(*
  Statement-only formalization of VERINA corpus artifact verina_basic_32,
  catalog title "swapFirstAndLast": the executable integer-array program swaps
  the first and last elements of a nonempty array and leaves every interior
  element unchanged. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory rich_listTheory;

val swapFirstAndLast_getD_def = new_definition (
  "swapFirstAndLast_getD_def",
  ``swapFirstAndLast_getD (xs : int list) (i : num) =
      if i < LENGTH xs then EL i xs else (0 : int)``
);

val swapFirstAndLast_precond_def = new_definition (
  "swapFirstAndLast_precond_def",
  ``swapFirstAndLast_precond (a : int list) <=>
      0 < LENGTH a``
);

val swapFirstAndLast_def = new_definition (
  "swapFirstAndLast_def",
  ``swapFirstAndLast (a : int list) =
      let first = swapFirstAndLast_getD a 0 in
      let last =
        swapFirstAndLast_getD a (LENGTH a - 1)
      in
      let a1 = LUPDATE last 0 a in
        LUPDATE first (LENGTH a - 1) a1``
);

val swapFirstAndLast_postcond_def = new_definition (
  "swapFirstAndLast_postcond_def",
  ``swapFirstAndLast_postcond
      (a : int list) (result : int list) <=>
      LENGTH result = LENGTH a /\
      swapFirstAndLast_getD result 0 =
        swapFirstAndLast_getD a (LENGTH a - 1) /\
      swapFirstAndLast_getD result (LENGTH result - 1) =
        swapFirstAndLast_getD a 0 /\
      EVERY
        (\i : num.
           swapFirstAndLast_getD result (i + 1) =
           swapFirstAndLast_getD a (i + 1))
        (COUNT_LIST (LENGTH result - 2))``
);

val swapFirstAndLast_spec_satisfied =
  ``!a : int list.
      swapFirstAndLast_precond a ==>
      swapFirstAndLast_postcond a (swapFirstAndLast a)``;
