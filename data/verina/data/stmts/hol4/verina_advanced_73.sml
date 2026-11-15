(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_73,
  catalog title "smallestMissing": the executable recursive scan of a strictly
  increasing natural-number list returns its smallest missing natural number
  under the stated correctness contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory;

val smallestMissing_pairwiseLt_def = Define `
  (smallestMissing_pairwiseLt ([] : num list) = T) /\
  (smallestMissing_pairwiseLt (x::xs) =
     (EVERY (\y : num. x < y) xs /\
      smallestMissing_pairwiseLt xs))
`;

val smallestMissing_precond_def = new_definition (
  "smallestMissing_precond_def",
  ``smallestMissing_precond (l : num list) <=>
      smallestMissing_pairwiseLt l``
);

val smallestMissing_search_def = Define `
  (smallestMissing_search
      ([] : num list) (n : num) =
     n) /\
  (smallestMissing_search
      (x::xs) n =
     if x = n then
       smallestMissing_search xs (n + 1)
     else if x > n then
       n
     else
       smallestMissing_search xs n)
`;

val smallestMissing_def = new_definition (
  "smallestMissing_def",
  ``smallestMissing (l : num list) =
      smallestMissing_search l 0``
);

val smallestMissing_postcond_def = new_definition (
  "smallestMissing_postcond_def",
  ``smallestMissing_postcond
      (l : num list) (result : num) <=>
      ~MEM result l /\
      !candidate : num.
        candidate < result ==>
        MEM candidate l``
);

val smallestMissing_spec_satisfied =
  ``!l : num list.
      smallestMissing_precond l ==>
      smallestMissing_postcond l (smallestMissing l)``;
