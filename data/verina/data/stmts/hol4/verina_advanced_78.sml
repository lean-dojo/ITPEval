(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_78,
  catalog title "twoSum": the executable left-to-right recursive search
  returns the unique increasing pair of indices whose integer values sum to
  the target under the exact pair-count precondition. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory optionTheory pairTheory;

val twoSum_nthD_def = Define `
  (twoSum_nthD
      (index : num) ([] : int list) = (0 : int)) /\
  (twoSum_nthD
      0 (x::xs) = x) /\
  (twoSum_nthD
      (SUC index) (x::xs) =
     twoSum_nthD index xs)
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
      1 < LENGTH nums /\
      twoSum_count target (twoSum_pairwiseSums nums) = 1``
);

val findComplementAux_def = Define `
  (findComplementAux
      ([] : int list)
      (target : int)
      (i : num)
      (x : int)
      (j : num) =
     NONE) /\
  (findComplementAux
      (y::ys)
      target
      i
      x
      j =
     if x + y = target then
       SOME (i + j + 1)
     else
       findComplementAux ys target i x (j + 1))
`;

val findComplement_def = new_definition (
  "findComplement_def",
  ``findComplement
      (nums : int list)
      (target : int)
      (i : num)
      (x : int) =
      findComplementAux nums target i x 0``
);

val twoSumAux_def = Define `
  (twoSumAux
      ([] : int list)
      (target : int)
      (i : num) =
     ((0, 0) : num # num)) /\
  (twoSumAux
      (x::xs)
      target
      i =
     case findComplement xs target i x of
       NONE => twoSumAux xs target (i + 1)
     | SOME j => (i, j))
`;

val twoSum_def = new_definition (
  "twoSum_def",
  ``twoSum
      (nums : int list) (target : int) =
      twoSumAux nums target 0``
);

val twoSum_postcond_def = new_definition (
  "twoSum_postcond_def",
  ``twoSum_postcond
      (nums : int list)
      (target : int)
      (result : num # num) <=>
      let i = FST result in
      let j = SND result in
        i < j /\
        i < LENGTH nums /\
        j < LENGTH nums /\
        twoSum_nthD i nums + twoSum_nthD j nums = target``
);

val twoSum_spec_satisfied =
  ``!(nums : int list) (target : int).
      twoSum_precond nums target ==>
      twoSum_postcond nums target (twoSum nums target)``;
