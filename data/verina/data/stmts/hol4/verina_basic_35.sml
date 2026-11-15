(*
  Statement-only formalization of VERINA corpus artifact verina_basic_35,
  catalog title "MoveZeroesToEnd": the executable integer-array program keeps
  the nonzero elements in order and moves all zero elements to the end, with
  its permutation and exact prefix/suffix contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory sortingTheory;

val MoveZeroesToEnd_precond_def = new_definition (
  "MoveZeroesToEnd_precond_def",
  ``MoveZeroesToEnd_precond (arr : int list) <=> T``
);

val MoveZeroesToEnd_def = new_definition (
  "MoveZeroesToEnd_def",
  ``MoveZeroesToEnd (arr : int list) =
      let nonZeros = FILTER (\x : int. x <> 0) arr in
      let zeros = FILTER (\x : int. x = 0) arr in
        nonZeros ++ zeros``
);

val MoveZeroesToEnd_idxOf_def = Define `
  (MoveZeroesToEnd_idxOf
      (value : int) ([] : int list) = 0) /\
  (MoveZeroesToEnd_idxOf
      value (head::tail) =
     if head = value then
       0
     else
       SUC (MoveZeroesToEnd_idxOf value tail))
`;

val MoveZeroesToEnd_postcond_def = new_definition (
  "MoveZeroesToEnd_postcond_def",
  ``MoveZeroesToEnd_postcond
      (arr : int list) (result : int list) <=>
      let firstResZeroIdx =
        MoveZeroesToEnd_idxOf (0 : int) result
      in
        PERM result arr /\
        TAKE firstResZeroIdx result =
          FILTER (\x : int. x <> 0) arr /\
        DROP firstResZeroIdx result =
          FILTER (\x : int. x = 0) arr``
);

val MoveZeroesToEnd_spec_satisfied =
  ``!arr : int list.
      MoveZeroesToEnd_precond arr ==>
      MoveZeroesToEnd_postcond
        arr (MoveZeroesToEnd arr)``;
