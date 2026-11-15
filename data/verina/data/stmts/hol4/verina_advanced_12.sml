(*
  Statement-only formalization of VERINA artifact verina_advanced_12,
  cataloged as "firstDuplicate": the recursive program returns the first
  integer whose second occurrence is encountered while scanning left to
  right, or NONE when the input list has no duplicates.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory optionTheory;

val firstDuplicate_precond_def = new_definition (
  "firstDuplicate_precond_def",
  ``firstDuplicate_precond (lst : int list) <=> T``
);

val firstDuplicate_helper_def = Define `
  (firstDuplicate_helper (seen : int list) ([] : int list) =
     (NONE : int option)) /\
  (firstDuplicate_helper seen (h::t) =
     if MEM h seen then
       SOME h
     else
       firstDuplicate_helper (h::seen) t)
`;

val firstDuplicate_def = new_definition (
  "firstDuplicate_def",
  ``firstDuplicate (lst : int list) =
      firstDuplicate_helper ([] : int list) lst``
);

val firstDuplicate_idxOf_def = Define `
  (firstDuplicate_idxOf (v : int) ([] : int list) = 0) /\
  (firstDuplicate_idxOf v (h::t) =
     if h = v then 0 else SUC (firstDuplicate_idxOf v t))
`;

val secondOccIdx_def = new_definition (
  "secondOccIdx_def",
  ``secondOccIdx (lst : int list) (v : int) =
      let first = firstDuplicate_idxOf v lst
      in
        first + 1 +
        firstDuplicate_idxOf v (DROP (first + 1) lst)``
);

val firstDuplicate_postcond_def = new_definition (
  "firstDuplicate_postcond_def",
  ``firstDuplicate_postcond
      (lst : int list) (result : int option) <=>
      case result of
        NONE => ALL_DISTINCT lst
      | SOME x =>
          LENGTH (FILTER (\y : int. y = x) lst) > 1 /\
          EVERY
            (\y : int.
              LENGTH (FILTER (\z : int. z = y) lst) = 1 \/
              secondOccIdx lst x <= secondOccIdx lst y)
            lst``
);

val firstDuplicate_spec_satisfied =
  ``!lst : int list.
      firstDuplicate_precond lst ==>
      firstDuplicate_postcond lst (firstDuplicate lst)``;
