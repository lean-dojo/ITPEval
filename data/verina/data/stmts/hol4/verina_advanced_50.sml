(*
  Statement-only formalization of VERINA artifact verina_advanced_50,
  cataloged as "mergeSorted": the executable indexed merge loop and drain
  functions combine two pairwise nondecreasing natural-number arrays into a
  pairwise nondecreasing permutation of their concatenation. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory sortingTheory;

val mergeSorted_pairwise_def = Define `
  (mergeSorted_pairwise ([] : num list) = T) /\
  (mergeSorted_pairwise (x::xs) =
     (EVERY (\y : num. x <= y) xs /\
      mergeSorted_pairwise xs))
`;

val mergeSorted_precond_def = new_definition (
  "mergeSorted_precond_def",
  ``mergeSorted_precond
      (a1 : num list) (a2 : num list) <=>
      mergeSorted_pairwise a1 /\
      mergeSorted_pairwise a2``
);

val mergeLoopFuel_def = Define `
  (mergeLoopFuel
      0
      (a1 : num list) (a2 : num list)
      (i : num) (j : num) (result : num list) =
     ((i,j),result)) /\
  (mergeLoopFuel
      (SUC fuel) a1 a2 i j result =
     if i < LENGTH a1 /\ j < LENGTH a2 then
       if EL i a1 <= EL j a2 then
         mergeLoopFuel fuel a1 a2 (i + 1) j
           (result ++ [EL i a1])
       else
         mergeLoopFuel fuel a1 a2 i (j + 1)
           (result ++ [EL j a2])
     else
       ((i,j),result))
`;

val mergeLoop_def = new_definition (
  "mergeLoop_def",
  ``mergeLoop
      (a1 : num list) (a2 : num list)
      (i : num) (j : num) (result : num list) =
      mergeLoopFuel
        ((LENGTH a1 - i) + (LENGTH a2 - j))
        a1 a2 i j result``
);

val drainFuel_def = Define `
  (drainFuel
      0 (arr : num list) (i : num) (result : num list) =
     result) /\
  (drainFuel
      (SUC fuel) arr i result =
     if i < LENGTH arr then
       drainFuel fuel arr (i + 1) (result ++ [EL i arr])
     else
       result)
`;

val drain_def = new_definition (
  "drain_def",
  ``drain
      (arr : num list) (i : num) (result : num list) =
      drainFuel (LENGTH arr - i) arr i result``
);

val mergeSorted_def = new_definition (
  "mergeSorted_def",
  ``mergeSorted (a1 : num list) (a2 : num list) =
      let loopResult = mergeLoop a1 a2 0 0 [] in
      let i = FST (FST loopResult) in
      let j = SND (FST loopResult) in
      let merged = SND loopResult in
      let withA1 = drain a1 i merged in
        drain a2 j withA1``
);

val mergeSorted_postcond_def = new_definition (
  "mergeSorted_postcond_def",
  ``mergeSorted_postcond
      (a1 : num list) (a2 : num list) (result : num list) <=>
      mergeSorted_pairwise result /\
      PERM result (a1 ++ a2)``
);

val mergeSorted_spec_satisfied =
  ``!(a1 : num list) (a2 : num list).
      mergeSorted_precond a1 a2 ==>
      mergeSorted_postcond a1 a2 (mergeSorted a1 a2)``;
