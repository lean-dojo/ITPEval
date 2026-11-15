(*
  Statement-only formalization of VERINA artifact verina_advanced_33,
  cataloged as "longestIncreasingSubsequence": the executable take-or-skip
  recursion returns an attained maximal length of a strictly increasing
  subsequence of an integer list. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory optionTheory;

val longestIncreasingSubsequence_precond_def = new_definition (
  "longestIncreasingSubsequence_precond_def",
  ``longestIncreasingSubsequence_precond (nums : int list) <=> T``
);

val longestIncreasingSubsequence_max2_def = new_definition (
  "longestIncreasingSubsequence_max2_def",
  ``longestIncreasingSubsequence_max2 (a : num) (b : num) =
      if a > b then a else b``
);

val longestIncreasingSubsequence_listLength_def = Define `
  (longestIncreasingSubsequence_listLength ([] : int list) = 0) /\
  (longestIncreasingSubsequence_listLength (x::xs) =
     1 + longestIncreasingSubsequence_listLength xs)
`;

val longestIncreasingSubsequence_helper_def = Define `
  (longestIncreasingSubsequence_helper
      ([] : int list) (prev : int option) = 0) /\
  (longestIncreasingSubsequence_helper
      (h::t) prev =
     let canTake =
       case prev of
         NONE => T
       | SOME p => p < h
     in
     let withTake =
       if canTake then
         1 + longestIncreasingSubsequence_helper t (SOME h)
       else
         0
     in
     let withoutTake =
       longestIncreasingSubsequence_helper t prev
     in
       longestIncreasingSubsequence_max2 withTake withoutTake)
`;

val longestIncreasingSubsequence_def = new_definition (
  "longestIncreasingSubsequence_def",
  ``longestIncreasingSubsequence (nums : int list) =
      longestIncreasingSubsequence_helper nums NONE``
);

val longestIncreasingSubsequence_allSubseq_def = new_definition (
  "longestIncreasingSubsequence_allSubseq_def",
  ``longestIncreasingSubsequence_allSubseq (nums : int list) =
      MAP REVERSE
        (FOLDL
          (\acc x. acc ++ MAP (\sub. x::sub) acc)
          ([[]] : int list list)
          nums)``
);

val longestIncreasingSubsequence_pairwiseLt_def = Define `
  (longestIncreasingSubsequence_pairwiseLt ([] : int list) = T) /\
  (longestIncreasingSubsequence_pairwiseLt (x::xs) =
     (EVERY (\y : int. x < y) xs /\
      longestIncreasingSubsequence_pairwiseLt xs))
`;

val longestIncreasingSubsequence_increasingSubseqLens_def =
  new_definition (
    "longestIncreasingSubsequence_increasingSubseqLens_def",
    ``longestIncreasingSubsequence_increasingSubseqLens
        (nums : int list) =
        MAP LENGTH
          (FILTER
            longestIncreasingSubsequence_pairwiseLt
            (longestIncreasingSubsequence_allSubseq nums))``
  );

val longestIncreasingSubsequence_postcond_def = new_definition (
  "longestIncreasingSubsequence_postcond_def",
  ``longestIncreasingSubsequence_postcond
      (nums : int list) (result : num) <=>
      MEM result
        (longestIncreasingSubsequence_increasingSubseqLens nums) /\
      EVERY
        (\len : num. len <= result)
        (longestIncreasingSubsequence_increasingSubseqLens nums)``
);

val longestIncreasingSubsequence_spec_satisfied =
  ``!nums : int list.
      longestIncreasingSubsequence_precond nums ==>
      longestIncreasingSubsequence_postcond
        nums (longestIncreasingSubsequence nums)``;
