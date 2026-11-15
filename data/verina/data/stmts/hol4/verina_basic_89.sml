(*
  Statement-only formalization of VERINA corpus artifact verina_basic_89,
  catalog title "SetToSeq": the executable left-fold program removes duplicate
  integers while preserving first-occurrence order and satisfies its exact
  membership, uniqueness, and order contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val SetToSeq_precond_def = new_definition (
  "SetToSeq_precond_def",
  ``SetToSeq_precond (s : int list) <=> T``
);

val SetToSeq_def = new_definition (
  "SetToSeq_def",
  ``SetToSeq (s : int list) =
      FOLDL
        (\acc x.
           if MEM x acc then acc else acc ++ [x])
        ([] : int list)
        s``
);

val SetToSeq_count_def = new_definition (
  "SetToSeq_count_def",
  ``SetToSeq_count (value : int) (xs : int list) =
      LENGTH (FILTER (\x : int. x = value) xs)``
);

val SetToSeq_idxOf_def = Define `
  (SetToSeq_idxOf
      (value : int) ([] : int list) = 0) /\
  (SetToSeq_idxOf
      value (head::tail) =
     if head = value then
       0
     else
       SUC (SetToSeq_idxOf value tail))
`;

val SetToSeq_pairwiseOrder_def = Define `
  (SetToSeq_pairwiseOrder
      (s : int list)
      (result : int list)
      ([] : int list) <=>
     T) /\
  (SetToSeq_pairwiseOrder
      s
      result
      (a::rest) <=>
     EVERY
       (\b : int.
          SetToSeq_idxOf a result <
            SetToSeq_idxOf b result ==>
          SetToSeq_idxOf a s <
            SetToSeq_idxOf b s)
       rest /\
     SetToSeq_pairwiseOrder s result rest)
`;

val SetToSeq_postcond_def = new_definition (
  "SetToSeq_postcond_def",
  ``SetToSeq_postcond
      (s : int list) (result : int list) <=>
      EVERY (\a : int. MEM a s) result /\
      EVERY (\a : int. MEM a result) s /\
      EVERY
        (\a : int. SetToSeq_count a result = 1)
        result /\
      SetToSeq_pairwiseOrder s result result``
);

val SetToSeq_spec_satisfied =
  ``!s : int list.
      SetToSeq_precond s ==>
      SetToSeq_postcond s (SetToSeq s)``;
