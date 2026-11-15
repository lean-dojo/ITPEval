(*
  Statement-only formalization of VERINA artifact verina_advanced_32,
  cataloged as "longestIncreasingSubsequence": the executable dynamic-
  programming scan returns an attained maximal length of a strictly
  increasing subsequence of an integer list. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val longestIncreasingSubsequence_precond_def = new_definition (
  "longestIncreasingSubsequence_precond_def",
  ``longestIncreasingSubsequence_precond (numbers : int list) <=> T``
);

val longestIncreasingSubsequence_natMax_def = new_definition (
  "longestIncreasingSubsequence_natMax_def",
  ``longestIncreasingSubsequence_natMax (m : num) (n : num) =
      if m < n then n else m``
);

val longestIncreasingSubsequence_findMaxLength_def = Define `
  (longestIncreasingSubsequence_findMaxLength ([] : num list) = 0) /\
  (longestIncreasingSubsequence_findMaxLength (x::xs) =
     let maxRest =
       longestIncreasingSubsequence_findMaxLength xs
     in
       if x > maxRest then x else maxRest)
`;

val longestIncreasingSubsequence_findLengthEndingAtCurr_def = Define `
  (longestIncreasingSubsequence_findLengthEndingAtCurr
      (currNum : int)
      ([] : int list)
      (lengths : num list)
      (best : num) =
     best) /\
  (longestIncreasingSubsequence_findLengthEndingAtCurr
      currNum
      (prevVal::restVals)
      ([] : num list)
      best =
     best) /\
  (longestIncreasingSubsequence_findLengthEndingAtCurr
      currNum
      (prevVal::restVals)
      (prevLen::restLens)
      best =
     if prevVal < currNum then
       longestIncreasingSubsequence_findLengthEndingAtCurr
         currNum restVals restLens
         (longestIncreasingSubsequence_natMax best prevLen)
     else
       longestIncreasingSubsequence_findLengthEndingAtCurr
         currNum restVals restLens best)
`;

val longestIncreasingSubsequence_buildTables_def = Define `
  (longestIncreasingSubsequence_buildTables
      ([] : int list)
      (prevNums : int list)
      (lengths : num list)
      (idx : num) =
     longestIncreasingSubsequence_findMaxLength lengths) /\
  (longestIncreasingSubsequence_buildTables
      (currNum::restNums)
      prevNums
      lengths
      idx =
     let bestPrevLen =
       longestIncreasingSubsequence_findLengthEndingAtCurr
         currNum prevNums lengths 0
     in
     let currLength = bestPrevLen + 1
     in
       longestIncreasingSubsequence_buildTables
         restNums
         (prevNums ++ [currNum])
         (lengths ++ [currLength])
         (idx + 1))
`;

val longestIncreasingSubsequence_def = Define `
  (longestIncreasingSubsequence ([] : int list) = 0) /\
  (longestIncreasingSubsequence [x] = 1) /\
  (longestIncreasingSubsequence (first::next::rest) =
     longestIncreasingSubsequence_buildTables
       (next::rest) [first] [1] 1)
`;

val longestIncreasingSubsequence_allSubseq_def = new_definition (
  "longestIncreasingSubsequence_allSubseq_def",
  ``longestIncreasingSubsequence_allSubseq (numbers : int list) =
      MAP REVERSE
        (FOLDL
          (\acc x. acc ++ MAP (\sub. x::sub) acc)
          ([[]] : int list list)
          numbers)``
);

val longestIncreasingSubsequence_pairwiseLt_def = Define `
  (longestIncreasingSubsequence_pairwiseLt ([] : int list) = T) /\
  (longestIncreasingSubsequence_pairwiseLt [x] = T) /\
  (longestIncreasingSubsequence_pairwiseLt (x::y::rest) =
     (x < y /\
      longestIncreasingSubsequence_pairwiseLt (y::rest)))
`;

val longestIncreasingSubsequence_increasingSubseqLens_def =
  new_definition (
    "longestIncreasingSubsequence_increasingSubseqLens_def",
    ``longestIncreasingSubsequence_increasingSubseqLens
        (numbers : int list) =
        MAP LENGTH
          (FILTER
            longestIncreasingSubsequence_pairwiseLt
            (longestIncreasingSubsequence_allSubseq numbers))``
  );

val longestIncreasingSubsequence_postcond_def = new_definition (
  "longestIncreasingSubsequence_postcond_def",
  ``longestIncreasingSubsequence_postcond
      (numbers : int list) (result : num) <=>
      MEM result
        (longestIncreasingSubsequence_increasingSubseqLens numbers) /\
      EVERY
        (\len : num. len <= result)
        (longestIncreasingSubsequence_increasingSubseqLens numbers)``
);

val longestIncreasingSubsequence_spec_satisfied =
  ``!numbers : int list.
      longestIncreasingSubsequence_precond numbers ==>
      longestIncreasingSubsequence_postcond
        numbers (longestIncreasingSubsequence numbers)``;
