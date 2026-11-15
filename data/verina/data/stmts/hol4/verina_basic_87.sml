(*
  Statement-only formalization of VERINA corpus artifact verina_basic_87,
  catalog title "SelectionSort": the executable integer-array selection-sort
  program repeatedly finds a minimum suffix index and swaps it into place,
  returning a pairwise nondecreasing permutation. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory sortingTheory;

val SelectionSort_getBang_def = new_definition (
  "SelectionSort_getBang_def",
  ``SelectionSort_getBang (a : int list) (i : num) =
      if i < LENGTH a then EL i a else (0 : int)``
);

val SelectionSort_setBang_def = new_definition (
  "SelectionSort_setBang_def",
  ``SelectionSort_setBang
      (a : int list) (i : num) (value : int) =
      if i < LENGTH a then LUPDATE value i a else a``
);

val SelectionSort_precond_def = new_definition (
  "SelectionSort_precond_def",
  ``SelectionSort_precond (a : int list) <=> T``
);

val findMinIndexInRangeFuel_def = Define `
  (findMinIndexInRangeFuel
      0
      (arr : int list)
      (start : num)
      (i : num)
      (minIdx : num) =
     minIdx) /\
  (findMinIndexInRangeFuel
      (SUC fuel)
      arr
      start
      i
      minIdx =
     let currIdx = start + i in
     let nextMinIdx =
       if SelectionSort_getBang arr currIdx <
          SelectionSort_getBang arr minIdx
       then
         currIdx
       else
         minIdx
     in
       findMinIndexInRangeFuel
         fuel arr start (i + 1) nextMinIdx)
`;

val findMinIndexInRange_def = new_definition (
  "findMinIndexInRange_def",
  ``findMinIndexInRange
      (arr : int list) (start : num) (finish : num) =
      findMinIndexInRangeFuel
        (finish - start) arr start 0 start``
);

val SelectionSort_swap_def = new_definition (
  "SelectionSort_swap_def",
  ``SelectionSort_swap
      (a : int list) (i : num) (j : num) =
      if i < LENGTH a /\ j < LENGTH a /\ i <> j then
        let temp = SelectionSort_getBang a i in
        let a1 =
          SelectionSort_setBang
            a i (SelectionSort_getBang a j)
        in
          SelectionSort_setBang a1 j temp
      else
        a``
);

val SelectionSort_foldFuel_def = Define `
  (SelectionSort_foldFuel
      0
      (arr : int list)
      (i : num)
      (finish : num) =
     arr) /\
  (SelectionSort_foldFuel
      (SUC fuel)
      arr
      i
      finish =
     let minIdx = findMinIndexInRange arr i finish in
     let nextArr = SelectionSort_swap arr i minIdx in
       SelectionSort_foldFuel
         fuel nextArr (i + 1) finish)
`;

val SelectionSort_def = new_definition (
  "SelectionSort_def",
  ``SelectionSort (a : int list) =
      SelectionSort_foldFuel
        (LENGTH a) a 0 (LENGTH a)``
);

val SelectionSort_pairwiseLe_def = Define `
  (SelectionSort_pairwiseLe ([] : int list) = T) /\
  (SelectionSort_pairwiseLe (x::xs) =
     (EVERY (\y : int. x <= y) xs /\
      SelectionSort_pairwiseLe xs))
`;

val SelectionSort_postcond_def = new_definition (
  "SelectionSort_postcond_def",
  ``SelectionSort_postcond
      (a : int list) (result : int list) <=>
      SelectionSort_pairwiseLe result /\
      PERM a result``
);

val SelectionSort_spec_satisfied =
  ``!a : int list.
      SelectionSort_precond a ==>
      SelectionSort_postcond a (SelectionSort a)``;
