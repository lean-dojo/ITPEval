(*
  Statement-only formalization of VERINA corpus artifact verina_basic_52,
  catalog title "BubbleSort": the executable bubble-sort program swaps
  adjacent out-of-order integers and returns a pairwise nondecreasing
  permutation of the input array. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory sortingTheory;

val BubbleSort_precond_def = new_definition (
  "BubbleSort_precond_def",
  ``BubbleSort_precond (a : int list) <=> T``
);

val BubbleSort_nthD_def = Define `
  (BubbleSort_nthD
      (index : num) ([] : int list) = (0 : int)) /\
  (BubbleSort_nthD
      0 (x::xs) = x) /\
  (BubbleSort_nthD
      (SUC index) (x::xs) =
     BubbleSort_nthD index xs)
`;

val BubbleSort_setD_def = new_definition (
  "BubbleSort_setD_def",
  ``BubbleSort_setD
      (a : int list) (index : num) (value : int) =
      if index < LENGTH a then
        LUPDATE value index a
      else
        a``
);

val swap_def = new_definition (
  "swap_def",
  ``swap (a : int list) (i : num) (j : num) =
      let temp = BubbleSort_nthD i a in
      let a1 =
        BubbleSort_setD a i (BubbleSort_nthD j a)
      in
        BubbleSort_setD a1 j temp``
);

val bubbleInnerFuel_def = Define `
  (bubbleInnerFuel
      0 (j : num) (i : num) (a : int list) =
     a) /\
  (bubbleInnerFuel
      (SUC fuel) j i a =
     if j < i then
       let a1 =
         if BubbleSort_nthD j a >
            BubbleSort_nthD (j + 1) a
         then
           swap a j (j + 1)
         else
           a
       in
         bubbleInnerFuel fuel (j + 1) i a1
     else
       a)
`;

val bubbleInner_def = new_definition (
  "bubbleInner_def",
  ``bubbleInner (j : num) (i : num) (a : int list) =
      bubbleInnerFuel (i - j) j i a``
);

val bubbleOuter_def = Define `
  (bubbleOuter 0 (a : int list) = a) /\
  (bubbleOuter (SUC i) a =
     let a1 = bubbleInner 0 (SUC i) a
     in
       bubbleOuter i a1)
`;

val BubbleSort_def = new_definition (
  "BubbleSort_def",
  ``BubbleSort (a : int list) =
      if LENGTH a = 0 then
        a
      else
        bubbleOuter (LENGTH a - 1) a``
);

val BubbleSort_pairwiseLe_def = Define `
  (BubbleSort_pairwiseLe ([] : int list) = T) /\
  (BubbleSort_pairwiseLe (x::xs) =
     (EVERY (\y : int. x <= y) xs /\
      BubbleSort_pairwiseLe xs))
`;

val BubbleSort_postcond_def = new_definition (
  "BubbleSort_postcond_def",
  ``BubbleSort_postcond
      (a : int list) (result : int list) <=>
      BubbleSort_pairwiseLe result /\
      PERM result a``
);

val BubbleSort_spec_satisfied =
  ``!a : int list.
      BubbleSort_precond a ==>
      BubbleSort_postcond a (BubbleSort a)``;
