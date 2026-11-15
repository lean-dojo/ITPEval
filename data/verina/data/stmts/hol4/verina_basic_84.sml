(*
  Statement-only formalization of VERINA corpus artifact verina_basic_84,
  catalog title "replace": the executable integer-array loop replaces every
  element strictly greater than the threshold with negative one, preserves
  all other elements and the array length, and has no precondition. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val replace_getBang_def = new_definition (
  "replace_getBang_def",
  ``replace_getBang (arr : int list) (i : num) =
      if i < LENGTH arr then EL i arr else (0 : int)``
);

val replace_precond_def = new_definition (
  "replace_precond_def",
  ``replace_precond (arr : int list) (k : int) <=> T``
);

val replace_loopFuel_def = Define `
  (replace_loopFuel
      0
      (oldArr : int list)
      (k : int)
      (i : num)
      (acc : int list) =
     acc) /\
  (replace_loopFuel
      (SUC fuel)
      oldArr
      k
      i
      acc =
     if i < LENGTH oldArr then
       if replace_getBang oldArr i > k then
         replace_loopFuel
           fuel oldArr k (i + 1)
           (LUPDATE (~1 : int) i acc)
       else
         replace_loopFuel fuel oldArr k (i + 1) acc
     else
       acc)
`;

val replace_loop_def = new_definition (
  "replace_loop_def",
  ``replace_loop
      (oldArr : int list)
      (k : int)
      (i : num)
      (acc : int list) =
      replace_loopFuel
        (SUC (LENGTH oldArr - i))
        oldArr k i acc``
);

val replace_def = new_definition (
  "replace_def",
  ``replace (arr : int list) (k : int) =
      replace_loop arr k 0 arr``
);

val replace_postcond_def = new_definition (
  "replace_postcond_def",
  ``replace_postcond
      (arr : int list)
      (k : int)
      (result : int list) <=>
      LENGTH result = LENGTH arr /\
      (!i : num.
         i < LENGTH arr ==>
         (replace_getBang arr i > k ==>
          replace_getBang result i = (~1 : int))) /\
      (!i : num.
         i < LENGTH arr ==>
         (replace_getBang arr i <= k ==>
          replace_getBang result i =
          replace_getBang arr i))``
);

val replace_spec_satisfied =
  ``!(arr : int list) (k : int).
      replace_precond arr k ==>
      replace_postcond arr k (replace arr k)``;
