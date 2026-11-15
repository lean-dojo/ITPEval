(*
  Statement-only formalization of VERINA artifact verina_advanced_36,
  cataloged as "majorityElement": the executable Boyer-Moore-style scan
  returns a natural number occurring strictly more than half the input-list
  length when such an element is guaranteed. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory optionTheory;

val countOccurrences_def = Define `
  (countOccurrences
      (target : num) ([] : num list) = 0) /\
  (countOccurrences target (y::ys) =
     if y = target then
       1 + countOccurrences target ys
     else
       countOccurrences target ys)
`;

val majorityElement_precond_def = new_definition (
  "majorityElement_precond_def",
  ``majorityElement_precond (xs : num list) <=>
      LENGTH xs > 0 /\
      EXISTS
        (\x : num.
          countOccurrences x xs > LENGTH xs DIV 2)
        xs``
);

val findCandidate_def = Define `
  (findCandidate
      ([] : num list)
      (candidate : num option)
      (count : num) =
     case candidate of
       NONE => 0
     | SOME c => c) /\
  (findCandidate (x::xs) candidate count =
     case candidate of
       NONE =>
         findCandidate xs (SOME x) 1
     | SOME c =>
         if x = c then
           findCandidate xs (SOME c) (count + 1)
         else if count = 0 then
           findCandidate xs (SOME x) 1
         else
           findCandidate xs (SOME c) (count - 1))
`;

val majorityElement_def = new_definition (
  "majorityElement_def",
  ``majorityElement (xs : num list) =
      findCandidate xs NONE 0``
);

val majorityElement_postcond_def = new_definition (
  "majorityElement_postcond_def",
  ``majorityElement_postcond
      (xs : num list) (result : num) <=>
      countOccurrences result xs > LENGTH xs DIV 2``
);

val majorityElement_spec_satisfied =
  ``!xs : num list.
      majorityElement_precond xs ==>
      majorityElement_postcond xs (majorityElement xs)``;
