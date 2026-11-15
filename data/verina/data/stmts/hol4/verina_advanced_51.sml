(*
  Statement-only formalization of VERINA artifact verina_advanced_51,
  cataloged as "mergeSorted": the executable recursive merge program combines
  two pairwise nondecreasing integer lists into a pairwise nondecreasing
  permutation of their concatenation. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory sortingTheory;

val mergeSorted_pairwise_def = Define `
  (mergeSorted_pairwise ([] : int list) = T) /\
  (mergeSorted_pairwise (x::xs) =
     (EVERY (\y : int. x <= y) xs /\
      mergeSorted_pairwise xs))
`;

val mergeSorted_precond_def = new_definition (
  "mergeSorted_precond_def",
  ``mergeSorted_precond
      (a : int list) (b : int list) <=>
      mergeSorted_pairwise a /\
      mergeSorted_pairwise b``
);

val mergeSortedAux_def = Define `
  (mergeSortedAux
      ([] : int list) (ys : int list) =
     ys) /\
  (mergeSortedAux
      (x::xs) ([] : int list) =
     x::xs) /\
  (mergeSortedAux
      (x::xs) (y::ys) =
     if x <= y then
       x::mergeSortedAux xs (y::ys)
     else
       y::mergeSortedAux (x::xs) ys)
`;

val mergeSorted_def = new_definition (
  "mergeSorted_def",
  ``mergeSorted
      (a : int list) (b : int list) =
      mergeSortedAux a b``
);

val mergeSorted_postcond_def = new_definition (
  "mergeSorted_postcond_def",
  ``mergeSorted_postcond
      (a : int list) (b : int list) (result : int list) <=>
      mergeSorted_pairwise result /\
      PERM result (a ++ b)``
);

val mergeSorted_spec_satisfied =
  ``!(a : int list) (b : int list).
      mergeSorted_precond a b ==>
      mergeSorted_postcond a b (mergeSorted a b)``;
