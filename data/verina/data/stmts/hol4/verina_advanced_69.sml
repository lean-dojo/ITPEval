(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_69,
  catalog title "searchInsert": the executable recursive search returns the
  first position in a strictly increasing integer list whose value is at least
  the target, or the list length if no such value exists, under the stated
  insertion-index correctness contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val searchInsert_pairwiseLt_def = Define `
  (searchInsert_pairwiseLt ([] : int list) = T) /\
  (searchInsert_pairwiseLt (x::xs) =
     (EVERY (\y : int. x < y) xs /\
      searchInsert_pairwiseLt xs))
`;

val searchInsert_precond_def = new_definition (
  "searchInsert_precond_def",
  ``searchInsert_precond
      (xs : int list) (target : int) <=>
      searchInsert_pairwiseLt xs``
);

val searchInsert_helper_def = Define `
  (searchInsert_helper
      (target : int) ([] : int list) (idx : num) =
     idx) /\
  (searchInsert_helper
      target (y::ys) idx =
     if target <= y then
       idx
     else
       searchInsert_helper target ys (idx + 1))
`;

val searchInsert_def = new_definition (
  "searchInsert_def",
  ``searchInsert (xs : int list) (target : int) =
      case xs of
        [] => 0
      | y::ys => searchInsert_helper target xs 0``
);

val searchInsert_getDefault_def = new_definition (
  "searchInsert_getDefault_def",
  ``searchInsert_getDefault
      (xs : int list) (index : num) =
      if index < LENGTH xs then
        EL index xs
      else
        (0 : int)``
);

val searchInsert_postcond_def = new_definition (
  "searchInsert_postcond_def",
  ``searchInsert_postcond
      (xs : int list)
      (target : int)
      (result : num) <=>
      result <= LENGTH xs /\
      EVERY
        (\i : num. searchInsert_getDefault xs i < target)
        (COUNT_LIST result) /\
      (result < LENGTH xs ==>
       target <= searchInsert_getDefault xs result)``
);

val searchInsert_spec_satisfied =
  ``!(xs : int list) (target : int).
      searchInsert_precond xs target ==>
      searchInsert_postcond
        xs target (searchInsert xs target)``;
