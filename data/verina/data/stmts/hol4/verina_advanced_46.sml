(*
  Statement-only formalization of VERINA artifact verina_advanced_46,
  cataloged as "maxSubarraySum": the executable all-negative check and
  Kadane-style scan return the greatest sum among all contiguous integer
  subarrays, including the empty subarray. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val maxSubarraySum_precond_def = new_definition (
  "maxSubarraySum_precond_def",
  ``maxSubarraySum_precond (numbers : int list) <=> T``
);

val maxSubarraySum_intMax_def = new_definition (
  "maxSubarraySum_intMax_def",
  ``maxSubarraySum_intMax (a : int) (b : int) =
      if a < b then b else a``
);

val maxSubarraySum_isAllNegative_def = Define `
  (maxSubarraySum_isAllNegative ([] : int list) = T) /\
  (maxSubarraySum_isAllNegative (x::xs) =
     if 0 <= x then F else maxSubarraySum_isAllNegative xs)
`;

val maxSubarraySum_findMaxProduct_def = Define `
  (maxSubarraySum_findMaxProduct
      ([] : int list) (currMax : int) (currSum : int) =
     currMax) /\
  (maxSubarraySum_findMaxProduct
      [x] currMax currSum =
     maxSubarraySum_intMax currMax x) /\
  (maxSubarraySum_findMaxProduct
      (x::y::rest) currMax currSum =
     let newSum =
       maxSubarraySum_intMax y (currSum + y)
     in
     let newMax =
       maxSubarraySum_intMax currMax newSum
     in
       maxSubarraySum_findMaxProduct
         (y::rest) newMax newSum)
`;

val maxSubarraySum_intToNat_def = new_definition (
  "maxSubarraySum_intToNat_def",
  ``maxSubarraySum_intToNat (value : int) =
      if value < 0 then 0 else Num value``
);

val maxSubarraySum_handleList_def = Define `
  (maxSubarraySum_handleList ([] : int list) = 0) /\
  (maxSubarraySum_handleList (x::xs) =
     if maxSubarraySum_isAllNegative (x::xs) then
       0
     else
       let initialMax = maxSubarraySum_intMax 0 x in
       let startSum = maxSubarraySum_intMax 0 x in
       let result =
         maxSubarraySum_findMaxProduct
           (x::xs) initialMax startSum
       in
         maxSubarraySum_intToNat result)
`;

val maxSubarraySum_def = new_definition (
  "maxSubarraySum_def",
  ``maxSubarraySum (numbers : int list) =
      int_of_num (maxSubarraySum_handleList numbers)``
);

val maxSubarraySum_subarraySum_def = new_definition (
  "maxSubarraySum_subarraySum_def",
  ``maxSubarraySum_subarraySum (subarray : int list) =
      FOLDL (\acc x. acc + x) 0 subarray``
);

val maxSubarraySum_subarraySums_def = new_definition (
  "maxSubarraySum_subarraySums_def",
  ``maxSubarraySum_subarraySums (numbers : int list) =
      FLAT
        (MAP
          (\start.
             MAP
               (\len.
                  maxSubarraySum_subarraySum
                    (TAKE len (DROP start numbers)))
               (COUNT_LIST (LENGTH numbers - start + 1)))
          (COUNT_LIST (LENGTH numbers + 1)))``
);

val maxSubarraySum_postcond_def = new_definition (
  "maxSubarraySum_postcond_def",
  ``maxSubarraySum_postcond
      (numbers : int list) (result : int) <=>
      let subArraySums = maxSubarraySum_subarraySums numbers
      in
        MEM result subArraySums /\
        EVERY (\sum : int. sum <= result) subArraySums``
);

val maxSubarraySum_spec_satisfied =
  ``!numbers : int list.
      maxSubarraySum_precond numbers ==>
      maxSubarraySum_postcond
        numbers (maxSubarraySum numbers)``;
