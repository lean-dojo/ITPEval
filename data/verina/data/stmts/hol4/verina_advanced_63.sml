(*
  Statement-only formalization of VERINA artifact verina_advanced_63,
  cataloged as "removeDuplicates": the executable recursive program counts
  the distinct values in a pairwise nondecreasing integer list and satisfies
  the stated erase-duplicates length contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val removeDuplicates_pairwise_def = Define `
  (removeDuplicates_pairwise ([] : int list) = T) /\
  (removeDuplicates_pairwise (x::xs) =
     (EVERY (\y : int. x <= y) xs /\
      removeDuplicates_pairwise xs))
`;

val removeDuplicates_precond_def = new_definition (
  "removeDuplicates_precond_def",
  ``removeDuplicates_precond (nums : int list) <=>
      removeDuplicates_pairwise nums``
);

val removeDuplicates_countUniques_def = Define `
  (removeDuplicates_countUniques
      (prev : int)
      ([] : int list)
      (k : num) =
     k) /\
  (removeDuplicates_countUniques
      prev
      (head::tail)
      k =
     if head = prev then
       removeDuplicates_countUniques prev tail k
     else
       removeDuplicates_countUniques head tail (k + 1))
`;

val removeDuplicates_def = Define `
  (removeDuplicates ([] : int list) = 0) /\
  (removeDuplicates (h::t) =
     removeDuplicates_countUniques h t 1)
`;

val removeDuplicates_eraseDupsLoop_def = Define `
  (removeDuplicates_eraseDupsLoop
      ([] : int list)
      (seen : int list) =
     REVERSE seen) /\
  (removeDuplicates_eraseDupsLoop
      (x::xs)
      seen =
     if MEM x seen then
       removeDuplicates_eraseDupsLoop xs seen
     else
       removeDuplicates_eraseDupsLoop xs (x::seen))
`;

val removeDuplicates_eraseDups_def = new_definition (
  "removeDuplicates_eraseDups_def",
  ``removeDuplicates_eraseDups (nums : int list) =
      removeDuplicates_eraseDupsLoop nums []``
);

val removeDuplicates_postcond_def = new_definition (
  "removeDuplicates_postcond_def",
  ``removeDuplicates_postcond
      (nums : int list) (result : num) <=>
      result - LENGTH (removeDuplicates_eraseDups nums) = 0 /\
      LENGTH (removeDuplicates_eraseDups nums) <= result``
);

val removeDuplicates_spec_satisfied =
  ``!nums : int list.
      removeDuplicates_precond nums ==>
      removeDuplicates_postcond nums (removeDuplicates nums)``;
