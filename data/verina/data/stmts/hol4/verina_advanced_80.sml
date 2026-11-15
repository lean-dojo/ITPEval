(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_80,
  catalog title "twoSum": under the unique-pair precondition, the exact
  fuel-bounded nested search returns two increasing in-bounds indices whose
  integer values sum to the target. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val twoSum_intNthD_def = Define `
  (twoSum_intNthD
      (index : num) ([] : int list) = (0 : int)) /\
  (twoSum_intNthD
      0 (x::xs) = x) /\
  (twoSum_intNthD
      (SUC index) (x::xs) =
     twoSum_intNthD index xs)
`;

val twoSum_numNthD_def = Define `
  (twoSum_numNthD
      (index : num) ([] : num list) = 0) /\
  (twoSum_numNthD
      0 (x::xs) = x) /\
  (twoSum_numNthD
      (SUC index) (x::xs) =
     twoSum_numNthD index xs)
`;

val twoSum_count_def = Define `
  (twoSum_count
      (target : int) ([] : int list) = 0) /\
  (twoSum_count
      target (x::xs) =
     if x = target then
       SUC (twoSum_count target xs)
     else
       twoSum_count target xs)
`;

val twoSum_pairwiseSums_def = Define `
  (twoSum_pairwiseSums
      ([] : int list) = ([] : int list)) /\
  (twoSum_pairwiseSums
      (x::xs) =
     MAP (\y : int. x + y) xs ++
       twoSum_pairwiseSums xs)
`;

val twoSum_precond_def = new_definition (
  "twoSum_precond_def",
  ``twoSum_precond
      (nums : int list) (target : int) <=>
      2 <= LENGTH nums /\
      MEM target (twoSum_pairwiseSums nums) /\
      twoSum_count target (twoSum_pairwiseSums nums) = 1``
);

val twoSum_findIndices_def = Define `
  (twoSum_findIndices
      (nums : int list)
      (target : int)
      (i : num)
      (j : num)
      0 =
     ([] : num list)) /\
  (twoSum_findIndices
      nums
      target
      i
      j
      (SUC fuel) =
     if LENGTH nums <= i then
       []
     else if LENGTH nums <= j then
       twoSum_findIndices nums target (i + 1) (i + 2) fuel
     else if
       twoSum_intNthD i nums + twoSum_intNthD j nums = target
     then
       [i; j]
     else
       twoSum_findIndices nums target i (j + 1) fuel)
`;

val twoSum_def = new_definition (
  "twoSum_def",
  ``twoSum
      (nums : int list) (target : int) =
      twoSum_findIndices
        nums target 0 1 (LENGTH nums * LENGTH nums)``
);

val twoSum_postcond_def = new_definition (
  "twoSum_postcond_def",
  ``twoSum_postcond
      (nums : int list)
      (target : int)
      (result : num list) <=>
      LENGTH result = 2 /\
      twoSum_numNthD 0 result < LENGTH nums /\
      twoSum_numNthD 1 result < LENGTH nums /\
      twoSum_numNthD 0 result < twoSum_numNthD 1 result /\
      twoSum_intNthD (twoSum_numNthD 0 result) nums +
        twoSum_intNthD (twoSum_numNthD 1 result) nums =
        target``
);

val twoSum_spec_satisfied =
  ``!(nums : int list) (target : int).
      twoSum_precond nums target ==>
      twoSum_postcond nums target (twoSum nums target)``;
