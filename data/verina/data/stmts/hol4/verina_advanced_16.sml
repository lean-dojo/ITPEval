(*
  Statement-only formalization of VERINA artifact verina_advanced_16,
  cataloged as "insertionSort": the executable insertion-sort program returns
  a pairwise nondecreasing permutation of its input integer list.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory sortingTheory;

val insertionSort_precond_def = new_definition (
  "insertionSort_precond_def",
  ``insertionSort_precond (xs : int list) <=> T``
);

val insertionSort_insert_def = Define `
  (insertionSort_insert (x : int) ([] : int list) = [x]) /\
  (insertionSort_insert x (y::ys) =
     if x <= y then
       x::y::ys
     else
       y::insertionSort_insert x ys)
`;

val insertionSort_sort_def = Define `
  (insertionSort_sort ([] : int list) = ([] : int list)) /\
  (insertionSort_sort (x::xs) =
     insertionSort_insert x (insertionSort_sort xs))
`;

val insertionSort_def = new_definition (
  "insertionSort_def",
  ``insertionSort (xs : int list) = insertionSort_sort xs``
);

val insertionSort_pairwise_def = Define `
  (insertionSort_pairwise ([] : int list) = T) /\
  (insertionSort_pairwise (x::xs) =
     (EVERY (\y : int. x <= y) xs /\
      insertionSort_pairwise xs))
`;

val insertionSort_postcond_def = new_definition (
  "insertionSort_postcond_def",
  ``insertionSort_postcond
      (xs : int list) (result : int list) <=>
      insertionSort_pairwise result /\
      PERM xs result``
);

val insertionSort_spec_satisfied =
  ``!xs : int list.
      insertionSort_precond xs ==>
      insertionSort_postcond xs (insertionSort xs)``;
