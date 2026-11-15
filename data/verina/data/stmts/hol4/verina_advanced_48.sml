(*
  Statement-only formalization of VERINA artifact verina_advanced_48,
  cataloged as "mergeSort": the executable insertion-sort implementation
  named mergeSort returns a pairwise nondecreasing permutation of its input
  integer list. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory sortingTheory;

val mergeSort_precond_def = new_definition (
  "mergeSort_precond_def",
  ``mergeSort_precond (list : int list) <=> T``
);

val mergeSort_insert_def = Define `
  (mergeSort_insert (x : int) ([] : int list) = [x]) /\
  (mergeSort_insert x (y::ys) =
     if x <= y then
       x::y::ys
     else
       y::mergeSort_insert x ys)
`;

val mergeSort_sort_def = Define `
  (mergeSort_sort ([] : int list) = ([] : int list)) /\
  (mergeSort_sort (x::xs) =
     mergeSort_insert x (mergeSort_sort xs))
`;

val mergeSort_def = new_definition (
  "mergeSort_def",
  ``mergeSort (list : int list) = mergeSort_sort list``
);

val mergeSort_pairwise_def = Define `
  (mergeSort_pairwise ([] : int list) = T) /\
  (mergeSort_pairwise (x::xs) =
     (EVERY (\y : int. x <= y) xs /\
      mergeSort_pairwise xs))
`;

val mergeSort_postcond_def = new_definition (
  "mergeSort_postcond_def",
  ``mergeSort_postcond
      (list : int list) (result : int list) <=>
      mergeSort_pairwise result /\
      PERM list result``
);

val mergeSort_spec_satisfied =
  ``!list : int list.
      mergeSort_precond list ==>
      mergeSort_postcond list (mergeSort list)``;
