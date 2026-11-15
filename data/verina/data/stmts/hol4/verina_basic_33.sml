(*
  Statement-only formalization of VERINA corpus artifact verina_basic_33,
  catalog title "smallestMissingNumber": the executable recursive scan of a
  non-decreasing natural-number list returns its smallest missing natural
  number under the stated correctness contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory;

val smallestMissingNumber_pairwiseLe_def = Define `
  (smallestMissingNumber_pairwiseLe ([] : num list) = T) /\
  (smallestMissingNumber_pairwiseLe (x::xs) =
     (EVERY (\y : num. x <= y) xs /\
      smallestMissingNumber_pairwiseLe xs))
`;

val smallestMissingNumber_precond_def = new_definition (
  "smallestMissingNumber_precond_def",
  ``smallestMissingNumber_precond (s : num list) <=>
      smallestMissingNumber_pairwiseLe s``
);

val smallestMissingNumber_findMissing_def = Define `
  (smallestMissingNumber_findMissing
      (v : num) ([] : num list) =
     v) /\
  (smallestMissingNumber_findMissing
      v (x::xs) =
     if x > v then
       v
     else if x = v then
       smallestMissingNumber_findMissing (v + 1) xs
     else
       smallestMissingNumber_findMissing v xs)
`;

val smallestMissingNumber_def = new_definition (
  "smallestMissingNumber_def",
  ``smallestMissingNumber (s : num list) =
      smallestMissingNumber_findMissing 0 s``
);

val smallestMissingNumber_postcond_def = new_definition (
  "smallestMissingNumber_postcond_def",
  ``smallestMissingNumber_postcond
      (s : num list) (result : num) <=>
      ~MEM result s /\
      !k : num.
        k < result ==>
        MEM k s``
);

val smallestMissingNumber_spec_satisfied =
  ``!s : num list.
      smallestMissingNumber_precond s ==>
      smallestMissingNumber_postcond
        s (smallestMissingNumber s)``;
