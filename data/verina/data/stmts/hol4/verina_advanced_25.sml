(*
  Statement-only formalization of VERINA artifact verina_advanced_25,
  cataloged as "lengthOfLIS": the executable dynamic-programming program
  returns an attained maximal length of a strictly increasing subsequence.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val lengthOfLIS_precond_def = new_definition (
  "lengthOfLIS_precond_def",
  ``lengthOfLIS_precond (nums : int list) <=> T``
);

val maxInArray_def = new_definition (
  "maxInArray_def",
  ``maxInArray (arr : num list) =
      FOLDL
        (\a b. if a >= b then a else b)
        0
        arr``
);

val lengthOfLIS_update_cell_def = new_definition (
  "lengthOfLIS_update_cell_def",
  ``lengthOfLIS_update_cell
      (nums : int list)
      (i : num)
      (dp : num list)
      (j : num) =
      if EL j nums < EL i nums /\ EL j dp + 1 > EL i dp then
        LUPDATE (EL j dp + 1) i dp
      else
        dp``
);

val lengthOfLIS_process_index_def = new_definition (
  "lengthOfLIS_process_index_def",
  ``lengthOfLIS_process_index
      (nums : int list)
      (dp : num list)
      (i : num) =
      FOLDL
        (\table j. lengthOfLIS_update_cell nums i table j)
        dp
        (GENLIST (\j. j) i)``
);

val lengthOfLIS_table_def = new_definition (
  "lengthOfLIS_table_def",
  ``lengthOfLIS_table (nums : int list) =
      let n = LENGTH nums in
      FOLDL
        (lengthOfLIS_process_index nums)
        (GENLIST (\k. 1) n)
        (GENLIST (\k. k + 1) (n - 1))``
);

val lengthOfLIS_def = new_definition (
  "lengthOfLIS_def",
  ``lengthOfLIS (nums : int list) =
      if NULL nums then
        0
      else
        maxInArray (lengthOfLIS_table nums)``
);

val lengthOfLIS_allSubseq_def = new_definition (
  "lengthOfLIS_allSubseq_def",
  ``lengthOfLIS_allSubseq (nums : int list) =
      MAP REVERSE
        (FOLDL
          (\acc x. acc ++ MAP (\sub. x::sub) acc)
          ([[]] : int list list)
          nums)``
);

val lengthOfLIS_pairwise_lt_def = Define `
  (lengthOfLIS_pairwise_lt ([] : int list) = T) /\
  (lengthOfLIS_pairwise_lt [x] = T) /\
  (lengthOfLIS_pairwise_lt (x::y::rest) =
     (x < y /\ lengthOfLIS_pairwise_lt (y::rest)))
`;

val lengthOfLIS_increasingSubseqLens_def = new_definition (
  "lengthOfLIS_increasingSubseqLens_def",
  ``lengthOfLIS_increasingSubseqLens (nums : int list) =
      MAP LENGTH
        (FILTER
          lengthOfLIS_pairwise_lt
          (lengthOfLIS_allSubseq nums))``
);

val lengthOfLIS_postcond_def = new_definition (
  "lengthOfLIS_postcond_def",
  ``lengthOfLIS_postcond
      (nums : int list)
      (result : num) <=>
      MEM result (lengthOfLIS_increasingSubseqLens nums) /\
      EVERY
        (\len : num. len <= result)
        (lengthOfLIS_increasingSubseqLens nums)``
);

val lengthOfLIS_spec_satisfied =
  ``!nums : int list.
      lengthOfLIS_precond nums ==>
      lengthOfLIS_postcond nums (lengthOfLIS nums)``;
