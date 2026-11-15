(*
  Statement-only formalization of VERINA artifact verina_advanced_29,
  cataloged as "longestGoodSubarray": the executable sliding-window program
  returns the maximum length of a contiguous natural-number subarray in which
  every value occurs at most k times. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory;

val longestGoodSubarray_precond_def = new_definition (
  "longestGoodSubarray_precond_def",
  ``longestGoodSubarray_precond
      (nums : num list) (k : num) <=>
      0 < k``
);

val longestGoodSubarray_freqLookup_def = Define `
  (longestGoodSubarray_freqLookup
      (x : num) ([] : (num # num) list) =
     0) /\
  (longestGoodSubarray_freqLookup
      x ((y, count)::rest) =
     if x = y then
       count
     else
       longestGoodSubarray_freqLookup x rest)
`;

val longestGoodSubarray_freqInsert_def = Define `
  (longestGoodSubarray_freqInsert
      (x : num) (count : num) ([] : (num # num) list) =
     [(x, count)]) /\
  (longestGoodSubarray_freqInsert
      x count ((y, oldCount)::rest) =
     if x = y then
       (x, count)::rest
     else
       (y, oldCount)::
         longestGoodSubarray_freqInsert x count rest)
`;

val longestGoodSubarray_freqErase_def = Define `
  (longestGoodSubarray_freqErase
      (x : num) ([] : (num # num) list) =
     ([] : (num # num) list)) /\
  (longestGoodSubarray_freqErase
      x ((y, count)::rest) =
     if x = y then
       rest
     else
       (y, count)::longestGoodSubarray_freqErase x rest)
`;

val longestGoodSubarray_tooFrequent_def = new_definition (
  "longestGoodSubarray_tooFrequent_def",
  ``longestGoodSubarray_tooFrequent
      (k : num) (freq : (num # num) list) <=>
      EXISTS (\entry. k < SND entry) freq``
);

val longestGoodSubarray_shrink_def = Define `
  (longestGoodSubarray_shrink
      0
      (nums : num list)
      (k : num)
      (left : num)
      (freq : (num # num) list) =
     (left, freq)) /\
  (longestGoodSubarray_shrink
      (SUC fuel)
      nums
      k
      left
      freq =
     if longestGoodSubarray_tooFrequent k freq then
       let leftNum = EL left nums in
       let leftCount =
         longestGoodSubarray_freqLookup leftNum freq in
       let nextFreq =
         if leftCount = 1 then
           longestGoodSubarray_freqErase leftNum freq
         else
           longestGoodSubarray_freqInsert
             leftNum (leftCount - 1) freq
       in
         longestGoodSubarray_shrink
           fuel nums k (left + 1) nextFreq
     else
       (left, freq))
`;

val longestGoodSubarray_natMax_def = new_definition (
  "longestGoodSubarray_natMax_def",
  ``longestGoodSubarray_natMax (m : num) (n : num) =
      if m < n then n else m``
);

val longestGoodSubarray_scan_def = Define `
  (longestGoodSubarray_scan
      (nums : num list)
      (k : num)
      ([] : num list)
      (right : num)
      (left : num)
      (maxLen : num)
      (freq : (num # num) list) =
     maxLen) /\
  (longestGoodSubarray_scan
      nums
      k
      (num::rest)
      right
      left
      maxLen
      freq =
     let count =
       longestGoodSubarray_freqLookup num freq in
     let insertedFreq =
       longestGoodSubarray_freqInsert num (count + 1) freq in
     let shrunk =
       longestGoodSubarray_shrink
         (LENGTH nums) nums k left insertedFreq in
     let nextLeft = FST shrunk in
     let nextFreq = SND shrunk in
     let windowLen = right - nextLeft + 1 in
     let nextMax =
       longestGoodSubarray_natMax maxLen windowLen
     in
       longestGoodSubarray_scan
         nums k rest (right + 1) nextLeft nextMax nextFreq)
`;

val longestGoodSubarray_def = new_definition (
  "longestGoodSubarray_def",
  ``longestGoodSubarray (nums : num list) (k : num) =
      longestGoodSubarray_scan
        nums k nums 0 0 0 ([] : (num # num) list)``
);

val longestGoodSubarray_subArrays_def = new_definition (
  "longestGoodSubarray_subArrays_def",
  ``longestGoodSubarray_subArrays (nums : num list) =
      FLAT
        (MAP
          (\start.
             MAP
               (\len. TAKE len (DROP start nums))
               (COUNT_LIST (LENGTH nums - start + 1)))
          (COUNT_LIST (LENGTH nums + 1)))``
);

val longestGoodSubarray_subArrayFreqs_def = new_definition (
  "longestGoodSubarray_subArrayFreqs_def",
  ``longestGoodSubarray_subArrayFreqs (nums : num list) =
      MAP
        (\arr.
           MAP
             (\x. LENGTH (FILTER (\y. y = x) arr))
             arr)
        (longestGoodSubarray_subArrays nums)``
);

val longestGoodSubarray_validSubArrayFreqs_def = new_definition (
  "longestGoodSubarray_validSubArrayFreqs_def",
  ``longestGoodSubarray_validSubArrayFreqs
      (nums : num list) (k : num) =
      FILTER
        (\freqs. EVERY (\count. count <= k) freqs)
        (longestGoodSubarray_subArrayFreqs nums)``
);

val longestGoodSubarray_postcond_def = new_definition (
  "longestGoodSubarray_postcond_def",
  ``longestGoodSubarray_postcond
      (nums : num list) (k : num) (result : num) <=>
      let validSubArrays =
        longestGoodSubarray_validSubArrayFreqs nums k
      in
        (nums = [] /\ result = 0) \/
        (nums <> [] /\
         EXISTS
           (\arr : num list. LENGTH arr = result)
           validSubArrays /\
         EVERY
           (\arr : num list. LENGTH arr <= result)
           validSubArrays)``
);

val longestGoodSubarray_spec_satisfied =
  ``!(nums : num list) (k : num).
      longestGoodSubarray_precond nums k ==>
      longestGoodSubarray_postcond
        nums k (longestGoodSubarray nums k)``;
