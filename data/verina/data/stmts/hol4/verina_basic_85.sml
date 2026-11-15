(*
  Statement-only formalization of VERINA corpus artifact verina_basic_85,
  catalog title "reverse": the executable integer-array program swaps
  symmetric elements from the ends inward, returning an array of unchanged
  length whose elements occur in reverse order. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val reverse_getBang_def = new_definition (
  "reverse_getBang_def",
  ``reverse_getBang (arr : int list) (i : num) =
      if i < LENGTH arr then EL i arr else (0 : int)``
);

val reverse_setBang_def = new_definition (
  "reverse_setBang_def",
  ``reverse_setBang
      (arr : int list) (i : num) (value : int) =
      if i < LENGTH arr then LUPDATE value i arr else arr``
);

val reverse_precond_def = new_definition (
  "reverse_precond_def",
  ``reverse_precond (a : int list) <=> T``
);

val reverse_coreFuel_def = Define `
  (reverse_coreFuel
      0
      (arr : int list)
      (i : num) =
     arr) /\
  (reverse_coreFuel
      (SUC fuel)
      arr
      i =
     if i < LENGTH arr DIV 2 then
       let j = LENGTH arr - 1 - i in
       let temp = reverse_getBang arr i in
       let arr1 =
         reverse_setBang arr i (reverse_getBang arr j)
       in
       let arr2 = reverse_setBang arr1 j temp in
         reverse_coreFuel fuel arr2 (i + 1)
     else
       arr)
`;

val reverse_core_def = new_definition (
  "reverse_core_def",
  ``reverse_core (arr : int list) (i : num) =
      reverse_coreFuel
        (SUC (LENGTH arr DIV 2 - i))
        arr
        i``
);

val reverse_def = new_definition (
  "reverse_def",
  ``reverse (a : int list) = reverse_core a 0``
);

val reverse_postcond_def = new_definition (
  "reverse_postcond_def",
  ``reverse_postcond
      (a : int list) (result : int list) <=>
      LENGTH result = LENGTH a /\
      (!i : num.
         i < LENGTH a ==>
         reverse_getBang result i =
         reverse_getBang a (LENGTH a - 1 - i))``
);

val reverse_spec_satisfied =
  ``!a : int list.
      reverse_precond a ==>
      reverse_postcond a (reverse a)``;
