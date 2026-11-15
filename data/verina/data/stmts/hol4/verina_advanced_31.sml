(*
  Statement-only formalization of VERINA artifact verina_advanced_31,
  cataloged as "longestIncreasingSubseqLength": the executable exhaustive
  subsequence search returns the maximum length of a strictly increasing
  subsequence of an integer list. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val longestIncreasingSubseqLength_precond_def = new_definition (
  "longestIncreasingSubseqLength_precond_def",
  ``longestIncreasingSubseqLength_precond (xs : int list) <=> T``
);

val longestIncreasingSubseqLength_subsequences_def = Define `
  (longestIncreasingSubseqLength_subsequences ([] : int list) =
     ([[]] : int list list)) /\
  (longestIncreasingSubseqLength_subsequences (x::xs) =
     let subs = longestIncreasingSubseqLength_subsequences xs
     in
       subs ++ MAP (\s. x::s) subs)
`;

val longestIncreasingSubseqLength_isStrictlyIncreasing_def = Define `
  (longestIncreasingSubseqLength_isStrictlyIncreasing
      ([] : int list) = T) /\
  (longestIncreasingSubseqLength_isStrictlyIncreasing
      [x] = T) /\
  (longestIncreasingSubseqLength_isStrictlyIncreasing
      (x::y::rest) =
     if x < y then
       longestIncreasingSubseqLength_isStrictlyIncreasing (y::rest)
     else
       F)
`;

val longestIncreasingSubseqLength_def = new_definition (
  "longestIncreasingSubseqLength_def",
  ``longestIncreasingSubseqLength (xs : int list) =
      FOLDL
        (\acc s.
           if acc < LENGTH s then LENGTH s else acc)
        0
        (FILTER
          longestIncreasingSubseqLength_isStrictlyIncreasing
          (longestIncreasingSubseqLength_subsequences xs))``
);

val longestIncreasingSubseqLength_allSubseq_def = new_definition (
  "longestIncreasingSubseqLength_allSubseq_def",
  ``longestIncreasingSubseqLength_allSubseq (xs : int list) =
      MAP REVERSE
        (FOLDL
          (\acc x. acc ++ MAP (\sub. x::sub) acc)
          ([[]] : int list list)
          xs)``
);

val longestIncreasingSubseqLength_pairwiseLt_def = Define `
  (longestIncreasingSubseqLength_pairwiseLt
      ([] : int list) = T) /\
  (longestIncreasingSubseqLength_pairwiseLt
      [x] = T) /\
  (longestIncreasingSubseqLength_pairwiseLt
      (x::y::rest) =
     (x < y /\
      longestIncreasingSubseqLength_pairwiseLt (y::rest)))
`;

val longestIncreasingSubseqLength_increasingSubseqLens_def =
  new_definition (
    "longestIncreasingSubseqLength_increasingSubseqLens_def",
    ``longestIncreasingSubseqLength_increasingSubseqLens
        (xs : int list) =
        MAP LENGTH
          (FILTER
            longestIncreasingSubseqLength_pairwiseLt
            (longestIncreasingSubseqLength_allSubseq xs))``
  );

val longestIncreasingSubseqLength_postcond_def = new_definition (
  "longestIncreasingSubseqLength_postcond_def",
  ``longestIncreasingSubseqLength_postcond
      (xs : int list) (result : num) <=>
      MEM result
        (longestIncreasingSubseqLength_increasingSubseqLens xs) /\
      EVERY
        (\len : num. len <= result)
        (longestIncreasingSubseqLength_increasingSubseqLens xs)``
);

val longestIncreasingSubseqLength_spec_satisfied =
  ``!xs : int list.
      longestIncreasingSubseqLength_precond xs ==>
      longestIncreasingSubseqLength_postcond
        xs (longestIncreasingSubseqLength xs)``;
