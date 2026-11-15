(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_81,
  catalog title "uniqueSorted": the executable duplicate-removal and insertion-
  sort program returns a permutation of the deduplicated integer input in
  pairwise nondecreasing order. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

val uniqueSorted_precond_def = new_definition (
  "uniqueSorted_precond_def",
  ``uniqueSorted_precond (arr : int list) <=> T``
);

val uniqueSorted_insert_def = Define `
  (uniqueSorted_insert
      (x : int) ([] : int list) =
     [x]) /\
  (uniqueSorted_insert
      x (head::tail) =
     if x <= head then
       x::head::tail
     else
       head::uniqueSorted_insert x tail)
`;

val uniqueSorted_insertionSort_def = Define `
  (uniqueSorted_insertionSort
      ([] : int list) =
     ([] : int list)) /\
  (uniqueSorted_insertionSort
      (h::t) =
     uniqueSorted_insert h
       (uniqueSorted_insertionSort t))
`;

val uniqueSorted_removeDupsAux_def = Define `
  (uniqueSorted_removeDupsAux
      ([] : int list)
      (seen : int list)
      (acc : int list) =
     REVERSE acc) /\
  (uniqueSorted_removeDupsAux
      (h::t)
      seen
      acc =
     if MEM h seen then
       uniqueSorted_removeDupsAux t seen acc
     else
       uniqueSorted_removeDupsAux
         t (h::seen) (h::acc))
`;

val uniqueSorted_removeDups_def = new_definition (
  "uniqueSorted_removeDups_def",
  ``uniqueSorted_removeDups (arr : int list) =
      uniqueSorted_removeDupsAux arr [] []``
);

val uniqueSorted_def = new_definition (
  "uniqueSorted_def",
  ``uniqueSorted (arr : int list) =
      uniqueSorted_insertionSort
        (uniqueSorted_removeDups arr)``
);

val uniqueSorted_pairwiseLe_def = Define `
  (uniqueSorted_pairwiseLe
      ([] : int list) <=>
     T) /\
  (uniqueSorted_pairwiseLe
      (head::tail) <=>
     EVERY (\x : int. head <= x) tail /\
     uniqueSorted_pairwiseLe tail)
`;

val uniqueSorted_postcond_def = new_definition (
  "uniqueSorted_postcond_def",
  ``uniqueSorted_postcond
      (arr : int list)
      (result : int list) <=>
      PERM (uniqueSorted_removeDups arr) result /\
      uniqueSorted_pairwiseLe result``
);

val uniqueSorted_spec_satisfied =
  ``!arr : int list.
      uniqueSorted_precond arr ==>
      uniqueSorted_postcond arr (uniqueSorted arr)``;
