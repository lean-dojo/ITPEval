(*
  Statement-only formalization of VERINA artifact verina_advanced_44,
  cataloged as "maxSubarraySumDivisibleByK": the executable prefix-sum
  program returns the maximum sum among nonempty contiguous integer
  subarrays whose length is divisible by k, defaulting to zero when no such
  subarray is found. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory optionTheory;

val maxSubarraySumDivisibleByK_precond_def = new_definition (
  "maxSubarraySumDivisibleByK_precond_def",
  ``maxSubarraySumDivisibleByK_precond
      (arr : int list) (k : int) <=>
      k > 0``
);

val maxSubarraySumDivisibleByK_prefixSumsAux_def = Define `
  (maxSubarraySumDivisibleByK_prefixSumsAux
      (acc : int) ([] : int list) =
     [acc]) /\
  (maxSubarraySumDivisibleByK_prefixSumsAux
      acc (x::xs) =
     acc ::
       maxSubarraySumDivisibleByK_prefixSumsAux
         (acc + x) xs)
`;

val maxSubarraySumDivisibleByK_prefixSums_def = new_definition (
  "maxSubarraySumDivisibleByK_prefixSums_def",
  ``maxSubarraySumDivisibleByK_prefixSums (arr : int list) =
      maxSubarraySumDivisibleByK_prefixSumsAux 0 arr``
);

val maxSubarraySumDivisibleByK_updateBest_def = new_definition (
  "maxSubarraySumDivisibleByK_updateBest_def",
  ``maxSubarraySumDivisibleByK_updateBest
      (best : int option) (subarraySum : int) =
      case best of
        NONE => SOME subarraySum
      | SOME b =>
          SOME (if b < subarraySum then subarraySum else b)``
);

val maxSubarraySumDivisibleByK_processStarts_def = Define `
  (maxSubarraySumDivisibleByK_processStarts
      (prefixSums : int list)
      (len : num)
      ([] : num list)
      (best : int option) =
     best) /\
  (maxSubarraySumDivisibleByK_processStarts
      prefixSums len (start::starts) best =
     let endIdx = start + len in
     let subarraySum =
       EL endIdx prefixSums - EL start prefixSums in
     let nextBest =
       maxSubarraySumDivisibleByK_updateBest best subarraySum
     in
       maxSubarraySumDivisibleByK_processStarts
         prefixSums len starts nextBest)
`;

val maxSubarraySumDivisibleByK_processLengths_def = Define `
  (maxSubarraySumDivisibleByK_processLengths
      (prefixSums : int list)
      (k : int)
      (n : num)
      ([] : num list)
      (best : int option) =
     best) /\
  (maxSubarraySumDivisibleByK_processLengths
      prefixSums k n (len::lens) best =
     let nextBest =
       if int_of_num len % k = 0 /\ 0 < len then
         maxSubarraySumDivisibleByK_processStarts
           prefixSums len (COUNT_LIST (n - len + 1)) best
       else
         best
     in
       maxSubarraySumDivisibleByK_processLengths
         prefixSums k n lens nextBest)
`;

val maxSubarraySumDivisibleByK_def = new_definition (
  "maxSubarraySumDivisibleByK_def",
  ``maxSubarraySumDivisibleByK
      (arr : int list) (k : int) =
      let n = LENGTH arr in
      if n = 0 \/ k = 0 then
        0
      else
        let prefixSums =
          maxSubarraySumDivisibleByK_prefixSums arr in
        let result =
          maxSubarraySumDivisibleByK_processLengths
            prefixSums k n (COUNT_LIST (n + 1)) NONE
        in
          case result of
            NONE => 0
          | SOME s => s``
);

val maxSubarraySumDivisibleByK_intToNat_def = new_definition (
  "maxSubarraySumDivisibleByK_intToNat_def",
  ``maxSubarraySumDivisibleByK_intToNat (k : int) =
      if k < 0 then 0 else Num k``
);

val maxSubarraySumDivisibleByK_subarrays_def = new_definition (
  "maxSubarraySumDivisibleByK_subarrays_def",
  ``maxSubarraySumDivisibleByK_subarrays (arr : int list) =
      FLAT
        (MAP
          (\start.
             MAP
               (\len. TAKE len (DROP start arr))
               (COUNT_LIST (LENGTH arr - start + 1)))
          (COUNT_LIST (LENGTH arr)))``
);

val maxSubarraySumDivisibleByK_divisibleSubarrays_def =
  new_definition (
    "maxSubarraySumDivisibleByK_divisibleSubarrays_def",
    ``maxSubarraySumDivisibleByK_divisibleSubarrays
        (arr : int list) (k : int) =
        FILTER
          (\subarray : int list.
             LENGTH subarray MOD
                 maxSubarraySumDivisibleByK_intToNat k = 0 /\
             0 < LENGTH subarray)
          (maxSubarraySumDivisibleByK_subarrays arr)``
  );

val maxSubarraySumDivisibleByK_subarraySum_def = new_definition (
  "maxSubarraySumDivisibleByK_subarraySum_def",
  ``maxSubarraySumDivisibleByK_subarraySum
      (subarray : int list) =
      FOLDL (\acc x. acc + x) 0 subarray``
);

val maxSubarraySumDivisibleByK_subarraySums_def = new_definition (
  "maxSubarraySumDivisibleByK_subarraySums_def",
  ``maxSubarraySumDivisibleByK_subarraySums
      (arr : int list) (k : int) =
      MAP
        maxSubarraySumDivisibleByK_subarraySum
        (maxSubarraySumDivisibleByK_divisibleSubarrays arr k)``
);

val maxSubarraySumDivisibleByK_postcond_def = new_definition (
  "maxSubarraySumDivisibleByK_postcond_def",
  ``maxSubarraySumDivisibleByK_postcond
      (arr : int list) (k : int) (result : int) <=>
      let subarraySums =
        maxSubarraySumDivisibleByK_subarraySums arr k
      in
        (LENGTH subarraySums = 0 ==> result = 0) /\
        (LENGTH subarraySums > 0 ==>
          MEM result subarraySums /\
          EVERY (\sum : int. sum <= result) subarraySums)``
);

val maxSubarraySumDivisibleByK_spec_satisfied =
  ``!(arr : int list) (k : int).
      maxSubarraySumDivisibleByK_postcond
        arr k (maxSubarraySumDivisibleByK arr k)``;
