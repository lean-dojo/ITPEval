(*
  Statement-only formalization of VERINA artifact verina_advanced_49,
  cataloged as "mergeSortedLists": the executable merge program combines two
  pairwise nondecreasing integer lists into a pairwise nondecreasing
  permutation of their concatenation. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory sortingTheory;

val mergeSortedLists_pairwise_def = Define `
  (mergeSortedLists_pairwise ([] : int list) = T) /\
  (mergeSortedLists_pairwise (x::xs) =
     (EVERY (\y : int. x <= y) xs /\
      mergeSortedLists_pairwise xs))
`;

val mergeSortedLists_precond_def = new_definition (
  "mergeSortedLists_precond_def",
  ``mergeSortedLists_precond
      (arr1 : int list) (arr2 : int list) <=>
      mergeSortedLists_pairwise arr1 /\
      mergeSortedLists_pairwise arr2``
);

val mergeSortedLists_merge_def = Define `
  (mergeSortedLists_merge
      ([] : int list) (ys : int list) =
     ys) /\
  (mergeSortedLists_merge
      (x::xs) ([] : int list) =
     x::xs) /\
  (mergeSortedLists_merge
      (x::xs) (y::ys) =
     if x <= y then
       x::mergeSortedLists_merge xs (y::ys)
     else
       y::mergeSortedLists_merge (x::xs) ys)
`;

val mergeSortedLists_def = new_definition (
  "mergeSortedLists_def",
  ``mergeSortedLists
      (arr1 : int list) (arr2 : int list) =
      mergeSortedLists_merge arr1 arr2``
);

val mergeSortedLists_postcond_def = new_definition (
  "mergeSortedLists_postcond_def",
  ``mergeSortedLists_postcond
      (arr1 : int list) (arr2 : int list) (result : int list) <=>
      mergeSortedLists_pairwise result /\
      PERM (arr1 ++ arr2) result``
);

val mergeSortedLists_spec_satisfied =
  ``!(arr1 : int list) (arr2 : int list).
      mergeSortedLists_precond arr1 arr2 ==>
      mergeSortedLists_postcond
        arr1 arr2 (mergeSortedLists arr1 arr2)``;
