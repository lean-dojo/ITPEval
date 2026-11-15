(*
  Statement-only formalization of VERINA artifact verina_advanced_56,
  cataloged as "moveZeroes": the executable stable partition moves all zeroes
  in an integer list to the end while preserving the nonzero order, together
  with its stated subsequence, suffix, count, and length contract. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val moveZeroes_precond_def = new_definition (
  "moveZeroes_precond_def",
  ``moveZeroes_precond (xs : int list) <=> T``
);

val countVal_def = Define `
  (countVal (val : int) ([] : int list) = 0) /\
  (countVal val (x::xs) =
     let rest = countVal val xs in
       if x = val then rest + 1 else rest)
`;

val isSubsequence_def = Define `
  (isSubsequence ([] : int list) (ys : int list) = T) /\
  (isSubsequence (x::xt) ([] : int list) = F) /\
  (isSubsequence (x::xt) (y::yt) =
     if x = y then
       isSubsequence xt yt
     else
       isSubsequence (x::xt) yt)
`;

val moveZeroes_def = new_definition (
  "moveZeroes_def",
  ``moveZeroes (xs : int list) =
      FILTER (\x : int. ~(x = 0)) xs ++
      FILTER (\x : int. x = 0) xs``
);

val moveZeroes_postcond_def = new_definition (
  "moveZeroes_postcond_def",
  ``moveZeroes_postcond
      (xs : int list) (result : int list) <=>
      isSubsequence
        (FILTER (\x : int. ~(x = 0)) xs)
        result = T /\
      EVERY
        (\x : int. x = 0)
        (dropWhile (\x : int. ~(x = 0)) result) /\
      countVal 0 xs = countVal 0 result /\
      LENGTH xs = LENGTH result``
);

val moveZeroes_spec_satisfied =
  ``!xs : int list.
      moveZeroes_precond xs ==>
      moveZeroes_postcond xs (moveZeroes xs)``;
