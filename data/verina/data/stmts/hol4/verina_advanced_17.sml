(*
  Statement-only formalization of VERINA artifact verina_advanced_17,
  cataloged as "insertionSort": the executable insertion-sort program returns
  a pairwise nondecreasing permutation of its input integer list.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory sortingTheory;

val insertionSort_precond_def = new_definition (
  "insertionSort_precond_def",
  ``insertionSort_precond (l : int list) <=> T``
);

val insertElement_def = Define `
  (insertElement (x : int) ([] : int list) = [x]) /\
  (insertElement x (y::ys) =
     if x <= y then
       x::y::ys
     else
       y::insertElement x ys)
`;

val sortList_def = Define `
  (sortList ([] : int list) = ([] : int list)) /\
  (sortList (x::xs) =
     insertElement x (sortList xs))
`;

val insertionSort_def = new_definition (
  "insertionSort_def",
  ``insertionSort (l : int list) = sortList l``
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
      (l : int list) (result : int list) <=>
      insertionSort_pairwise result /\
      PERM l result``
);

val insertionSort_spec_satisfied =
  ``!l : int list.
      insertionSort_precond l ==>
      insertionSort_postcond l (insertionSort l)``;
