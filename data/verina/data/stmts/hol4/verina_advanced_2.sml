(*
  Statement-only formalization of VERINA artifact verina_advanced_2,
  cataloged as "LongestCommonSubsequence": the dynamic-programming program
  returns the greatest length among common subsequences of two integer arrays.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val LongestCommonSubsequence_precond_def = new_definition (
  "LongestCommonSubsequence_precond_def",
  ``LongestCommonSubsequence_precond
      (a : int list) (b : int list) <=> T``
);

val intMax_def = new_definition (
  "intMax_def",
  ``intMax (x : int) (y : int) =
      if x < y then y else x``
);

val lcs_initial_table_def = new_definition (
  "lcs_initial_table_def",
  ``lcs_initial_table (a : int list) (b : int list) =
      GENLIST
        (\i. GENLIST (\j. (0 : int)) (LENGTH b + 1))
        (LENGTH a + 1)``
);

val lcs_update_cell_def = new_definition (
  "lcs_update_cell_def",
  ``lcs_update_cell
      (a : int list)
      (b : int list)
      (i : num)
      (j : num)
      (dp : int list list) =
      if i = 0 \/ j = 0 then
        dp
      else if EL (i - 1) a = EL (j - 1) b then
        let newVal = EL (j - 1) (EL (i - 1) dp) + 1
        in
          LUPDATE (LUPDATE newVal j (EL i dp)) i dp
      else
        let newVal =
          intMax
            (EL j (EL (i - 1) dp))
            (EL (j - 1) (EL i dp))
        in
          LUPDATE (LUPDATE newVal j (EL i dp)) i dp``
);

val lcs_process_row_def = new_definition (
  "lcs_process_row_def",
  ``lcs_process_row
      (a : int list)
      (b : int list)
      (dp : int list list)
      (i : num) =
      FOLDL
        (\table j. lcs_update_cell a b i j table)
        dp
        (GENLIST (\j. j) (LENGTH b + 1))``
);

val lcs_table_def = new_definition (
  "lcs_table_def",
  ``lcs_table (a : int list) (b : int list) =
      FOLDL
        (lcs_process_row a b)
        (lcs_initial_table a b)
        (GENLIST (\i. i) (LENGTH a + 1))``
);

val LongestCommonSubsequence_def = new_definition (
  "LongestCommonSubsequence_def",
  ``LongestCommonSubsequence (a : int list) (b : int list) =
      EL (LENGTH b) (EL (LENGTH a) (lcs_table a b))``
);

val allSubseq_def = new_definition (
  "allSubseq_def",
  ``allSubseq (arr : int list) =
      MAP REVERSE
        (FOLDL
          (\acc x. acc ++ MAP (\s. x::s) acc)
          ([[]] : int list list)
          arr)``
);

val commonSubseqLens_def = new_definition (
  "commonSubseqLens_def",
  ``commonSubseqLens (a : int list) (b : int list) =
      MAP
        (\s. int_of_num (LENGTH s))
        (FILTER
          (\s : int list. MEM s (allSubseq b))
          (allSubseq a))``
);

val LongestCommonSubsequence_postcond_def = new_definition (
  "LongestCommonSubsequence_postcond_def",
  ``LongestCommonSubsequence_postcond
      (a : int list) (b : int list) (result : int) <=>
      MEM result (commonSubseqLens a b) /\
      EVERY
        (\len : int. len <= result)
        (commonSubseqLens a b)``
);

val LongestCommonSubsequence_spec_satisfied =
  ``!(a : int list) (b : int list).
      LongestCommonSubsequence_precond a b ==>
      LongestCommonSubsequence_postcond
        a b (LongestCommonSubsequence a b)``;
