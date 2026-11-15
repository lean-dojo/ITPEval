(*
  Statement-only formalization of VERINA artifact verina_advanced_4,
  cataloged as "LongestIncreasingSubsequence": the executable dynamic-
  programming program returns an attained maximal length of a strictly
  increasing subsequence of an integer array. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val LongestIncreasingSubsequence_precond_def = new_definition (
  "LongestIncreasingSubsequence_precond_def",
  ``LongestIncreasingSubsequence_precond (a : int list) <=> T``
);

val intMax_def = new_definition (
  "intMax_def",
  ``intMax (x : int) (y : int) =
      if x < y then y else x``
);

val LongestIncreasingSubsequence_update_cell_def = new_definition (
  "LongestIncreasingSubsequence_update_cell_def",
  ``LongestIncreasingSubsequence_update_cell
      (a : int list)
      (i : num)
      (dp : int list)
      (j : num) =
      if EL j a < EL i a then
        let newVal = intMax (EL i dp) (EL j dp + 1)
        in
          LUPDATE newVal i dp
      else
        dp``
);

val LongestIncreasingSubsequence_process_index_def = new_definition (
  "LongestIncreasingSubsequence_process_index_def",
  ``LongestIncreasingSubsequence_process_index
      (a : int list)
      (dp : int list)
      (i : num) =
      FOLDL
        (\table j.
           LongestIncreasingSubsequence_update_cell a i table j)
        dp
        (GENLIST (\j. j) i)``
);

val LongestIncreasingSubsequence_table_def = new_definition (
  "LongestIncreasingSubsequence_table_def",
  ``LongestIncreasingSubsequence_table (a : int list) =
      let n = LENGTH a in
      FOLDL
        (LongestIncreasingSubsequence_process_index a)
        (GENLIST (\k. (1 : int)) n)
        (GENLIST (\k. k + 1) (n - 1))``
);

val LongestIncreasingSubsequence_def = new_definition (
  "LongestIncreasingSubsequence_def",
  ``LongestIncreasingSubsequence (a : int list) =
      FOLDL intMax 0 (LongestIncreasingSubsequence_table a)``
);

val LongestIncreasingSubsequence_allSubseq_def = new_definition (
  "LongestIncreasingSubsequence_allSubseq_def",
  ``LongestIncreasingSubsequence_allSubseq (a : int list) =
      MAP REVERSE
        (FOLDL
          (\acc x. acc ++ MAP (\sub. x::sub) acc)
          ([[]] : int list list)
          a)``
);

val LongestIncreasingSubsequence_pairwiseLt_def = Define `
  (LongestIncreasingSubsequence_pairwiseLt ([] : int list) = T) /\
  (LongestIncreasingSubsequence_pairwiseLt (x::xs) =
     (EVERY (\y : int. x < y) xs /\
      LongestIncreasingSubsequence_pairwiseLt xs))
`;

val LongestIncreasingSubsequence_increasingSubseqLens_def =
  new_definition (
    "LongestIncreasingSubsequence_increasingSubseqLens_def",
    ``LongestIncreasingSubsequence_increasingSubseqLens
        (a : int list) =
        MAP
          (\sub : int list. int_of_num (LENGTH sub))
          (FILTER
            LongestIncreasingSubsequence_pairwiseLt
            (LongestIncreasingSubsequence_allSubseq a))``
  );

val LongestIncreasingSubsequence_postcond_def = new_definition (
  "LongestIncreasingSubsequence_postcond_def",
  ``LongestIncreasingSubsequence_postcond
      (a : int list) (result : int) <=>
      MEM result
        (LongestIncreasingSubsequence_increasingSubseqLens a) /\
      EVERY
        (\len : int. len <= result)
        (LongestIncreasingSubsequence_increasingSubseqLens a)``
);

val LongestIncreasingSubsequence_spec_satisfied =
  ``!a : int list.
      LongestIncreasingSubsequence_precond a ==>
      LongestIncreasingSubsequence_postcond
        a (LongestIncreasingSubsequence a)``;
