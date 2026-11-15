(*
  Statement-only formalization of VERINA artifact verina_advanced_24,
  cataloged as "lengthOfLIS": the executable patience-sorting program returns
  a length that is attained by a strictly increasing subsequence and is
  maximal among all strictly increasing subsequences. This file contains no
  proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val lengthOfLIS_precond_def = new_definition (
  "lengthOfLIS_precond_def",
  ``lengthOfLIS_precond (nums : int list) <=> T``
);

val lengthOfLIS_replace_def = Define `
  (lengthOfLIS_replace
      (x : int) ([] : int list) (acc : int list) =
     REVERSE acc ++ [x]) /\
  (lengthOfLIS_replace x (y::ys) acc =
     if x <= y then
       REVERSE acc ++ (x::ys)
     else
       lengthOfLIS_replace x ys (y::acc))
`;

val lengthOfLIS_helper_def = new_definition (
  "lengthOfLIS_helper_def",
  ``lengthOfLIS_helper (dp : int list) (x : int) =
      lengthOfLIS_replace x dp []``
);

val lengthOfLIS_def = new_definition (
  "lengthOfLIS_def",
  ``lengthOfLIS (nums : int list) =
      int_of_num (LENGTH (FOLDL lengthOfLIS_helper [] nums))``
);

val lengthOfLIS_isStrictlyIncreasing_def = Define `
  (lengthOfLIS_isStrictlyIncreasing ([] : int list) = T) /\
  (lengthOfLIS_isStrictlyIncreasing [x] = T) /\
  (lengthOfLIS_isStrictlyIncreasing (x::y::rest) =
     (x < y /\ lengthOfLIS_isStrictlyIncreasing (y::rest)))
`;

val lengthOfLIS_subsequences_def = Define `
  (lengthOfLIS_subsequences ([] : int list) =
     ([[]] : int list list)) /\
  (lengthOfLIS_subsequences (x::xs) =
     let rest = lengthOfLIS_subsequences xs
     in
       rest ++ MAP (\r. x::r) rest)
`;

val lengthOfLIS_allIncreasing_def = new_definition (
  "lengthOfLIS_allIncreasing_def",
  ``lengthOfLIS_allIncreasing (nums : int list) =
      FILTER
        lengthOfLIS_isStrictlyIncreasing
        (lengthOfLIS_subsequences nums)``
);

val lengthOfLIS_postcond_def = new_definition (
  "lengthOfLIS_postcond_def",
  ``lengthOfLIS_postcond
      (nums : int list) (result : int) <=>
      let allIncreasing = lengthOfLIS_allIncreasing nums
      in
        EXISTS
          (\l : int list. int_of_num (LENGTH l) = result)
          allIncreasing /\
        EVERY
          (\l : int list. int_of_num (LENGTH l) <= result)
          allIncreasing``
);

val lengthOfLIS_spec_satisfied =
  ``!nums : int list.
      lengthOfLIS_precond nums ==>
      lengthOfLIS_postcond nums (lengthOfLIS nums)``;
