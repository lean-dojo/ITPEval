(*
  Statement-only formalization of VERINA artifact verina_advanced_45,
  cataloged as "maxSubarraySum": the executable Kadane scan returns the
  maximum sum of a nonempty contiguous subarray of an integer list, with
  result zero for the empty list. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val maxSubarraySum_precond_def = new_definition (
  "maxSubarraySum_precond_def",
  ``maxSubarraySum_precond (xs : int list) <=> T``
);

val maxSubarraySum_intMax_def = new_definition (
  "maxSubarraySum_intMax_def",
  ``maxSubarraySum_intMax (a : int) (b : int) =
      if a < b then b else a``
);

val maxSubarraySum_helper_def = Define `
  (maxSubarraySum_helper
      ([] : int list) (curMax : int) (globalMax : int) =
     globalMax) /\
  (maxSubarraySum_helper
      (x::xs) curMax globalMax =
     let newCurMax =
       maxSubarraySum_intMax x (curMax + x)
     in
     let newGlobal =
       maxSubarraySum_intMax globalMax newCurMax
     in
       maxSubarraySum_helper xs newCurMax newGlobal)
`;

val maxSubarraySum_def = Define `
  (maxSubarraySum ([] : int list) = 0) /\
  (maxSubarraySum (x::xs) =
     maxSubarraySum_helper xs x x)
`;

val maxSubarraySum_subarraySum_def = new_definition (
  "maxSubarraySum_subarraySum_def",
  ``maxSubarraySum_subarraySum (subarray : int list) =
      FOLDL (\acc x. acc + x) 0 subarray``
);

val maxSubarraySum_subarraySums_def = new_definition (
  "maxSubarraySum_subarraySums_def",
  ``maxSubarraySum_subarraySums (xs : int list) =
      FLAT
        (MAP
          (\start.
             MAP
               (\len.
                  maxSubarraySum_subarraySum
                    (TAKE len (DROP start xs)))
               (GENLIST
                 (\offset. offset + 1)
                 (LENGTH xs - start)))
          (COUNT_LIST (LENGTH xs + 1)))``
);

val maxSubarraySum_postcond_def = new_definition (
  "maxSubarraySum_postcond_def",
  ``maxSubarraySum_postcond
      (xs : int list) (result : int) <=>
      if xs = [] then
        result = 0
      else
        MEM result (maxSubarraySum_subarraySums xs) /\
        EVERY
          (\sum : int. sum <= result)
          (maxSubarraySum_subarraySums xs)``
);

val maxSubarraySum_spec_satisfied =
  ``!xs : int list.
      maxSubarraySum_precond xs ==>
      maxSubarraySum_postcond xs (maxSubarraySum xs)``;
