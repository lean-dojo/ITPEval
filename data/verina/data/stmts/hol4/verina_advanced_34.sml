(*
  Statement-only formalization of VERINA artifact verina_advanced_34,
  cataloged as "longestIncreasingSubsequence": the executable patience-
  sorting scan uses left-biased binary search to return an attained maximal
  length of a strictly increasing integer subsequence. This file contains no
  proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val longestIncreasingSubsequence_precond_def = new_definition (
  "longestIncreasingSubsequence_precond_def",
  ``longestIncreasingSubsequence_precond (nums : int list) <=> T``
);

val binarySearchLeft_arrayGet_def = Define `
  (binarySearchLeft_arrayGet
      ([] : int list) (index : num) = 0) /\
  (binarySearchLeft_arrayGet
      (x::xs) 0 = x) /\
  (binarySearchLeft_arrayGet
      (x::xs) (SUC index) =
     binarySearchLeft_arrayGet xs index)
`;

val binarySearchLeft_fuel_def = Define `
  (binarySearchLeft_fuel
      (sub : int list)
      (num : int)
      (left : num)
      (right : num)
      0 =
     left) /\
  (binarySearchLeft_fuel
      sub num left right (SUC fuel) =
     if left < right then
       let mid = (left + right) DIV 2 in
       let midValue = binarySearchLeft_arrayGet sub mid in
         if midValue = num then
           binarySearchLeft_fuel sub num left mid fuel
         else if midValue < num then
           binarySearchLeft_fuel sub num (mid + 1) right fuel
         else
           binarySearchLeft_fuel sub num left mid fuel
     else
       left)
`;

val binarySearchLeft_def = new_definition (
  "binarySearchLeft_def",
  ``binarySearchLeft
      (sub : int list)
      (num : int)
      (left : num)
      (right : num) =
      binarySearchLeft_fuel sub num left right (right - left)``
);

val longestIncreasingSubsequence_arraySet_def = Define `
  (longestIncreasingSubsequence_arraySet
      ([] : int list) (index : num) (value : int) =
     ([] : int list)) /\
  (longestIncreasingSubsequence_arraySet
      (x::xs) 0 value =
     value::xs) /\
  (longestIncreasingSubsequence_arraySet
      (x::xs) (SUC index) value =
     x::longestIncreasingSubsequence_arraySet xs index value)
`;

val longestIncreasingSubsequence_scan_def = Define `
  (longestIncreasingSubsequence_scan
      ([] : int list) (sub : int list) =
     sub) /\
  (longestIncreasingSubsequence_scan
      (num::rest) sub =
     let right = LENGTH sub - 1 in
     let lastValue = binarySearchLeft_arrayGet sub right in
       if lastValue < num then
         longestIncreasingSubsequence_scan rest (sub ++ [num])
       else
         let left = binarySearchLeft sub num 0 right in
           longestIncreasingSubsequence_scan
             rest
             (longestIncreasingSubsequence_arraySet sub left num))
`;

val longestIncreasingSubsequence_def = Define `
  (longestIncreasingSubsequence ([] : int list) = 0) /\
  (longestIncreasingSubsequence (first::rest) =
     int_of_num
       (LENGTH
         (longestIncreasingSubsequence_scan rest [first])))
`;

val longestIncreasingSubsequence_allSubseq_def = new_definition (
  "longestIncreasingSubsequence_allSubseq_def",
  ``longestIncreasingSubsequence_allSubseq (nums : int list) =
      MAP REVERSE
        (FOLDL
          (\acc x. acc ++ MAP (\sub. x::sub) acc)
          ([[]] : int list list)
          nums)``
);

val longestIncreasingSubsequence_pairwiseLt_def = Define `
  (longestIncreasingSubsequence_pairwiseLt ([] : int list) = T) /\
  (longestIncreasingSubsequence_pairwiseLt (x::xs) =
     (EVERY (\y : int. x < y) xs /\
      longestIncreasingSubsequence_pairwiseLt xs))
`;

val longestIncreasingSubsequence_increasingSubseqLens_def =
  new_definition (
    "longestIncreasingSubsequence_increasingSubseqLens_def",
    ``longestIncreasingSubsequence_increasingSubseqLens
        (nums : int list) =
        MAP
          (\sub : int list. int_of_num (LENGTH sub))
          (FILTER
            longestIncreasingSubsequence_pairwiseLt
            (longestIncreasingSubsequence_allSubseq nums))``
  );

val longestIncreasingSubsequence_postcond_def = new_definition (
  "longestIncreasingSubsequence_postcond_def",
  ``longestIncreasingSubsequence_postcond
      (nums : int list) (result : int) <=>
      MEM result
        (longestIncreasingSubsequence_increasingSubseqLens nums) /\
      EVERY
        (\len : int. len <= result)
        (longestIncreasingSubsequence_increasingSubseqLens nums)``
);

val longestIncreasingSubsequence_spec_satisfied =
  ``!nums : int list.
      longestIncreasingSubsequence_precond nums ==>
      longestIncreasingSubsequence_postcond
        nums (longestIncreasingSubsequence nums)``;
