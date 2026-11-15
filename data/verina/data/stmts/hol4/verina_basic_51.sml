(*
  Statement-only formalization of VERINA corpus artifact verina_basic_51,
  catalog title "BinarySearch": the executable lower-bound binary search on a
  nondecreasing integer array returns the first insertion index separating
  entries below the key from entries at least the key. This file contains no
  proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val BinarySearch_pairwiseLe_def = Define `
  (BinarySearch_pairwiseLe ([] : int list) = T) /\
  (BinarySearch_pairwiseLe (x::xs) =
     (EVERY (\y : int. x <= y) xs /\
      BinarySearch_pairwiseLe xs))
`;

val BinarySearch_precond_def = new_definition (
  "BinarySearch_precond_def",
  ``BinarySearch_precond
      (a : int list) (key : int) <=>
      BinarySearch_pairwiseLe a``
);

val BinarySearch_nthD_def = Define `
  (BinarySearch_nthD
      (index : num) ([] : int list) = (0 : int)) /\
  (BinarySearch_nthD
      0 (x::xs) = x) /\
  (BinarySearch_nthD
      (SUC index) (x::xs) =
     BinarySearch_nthD index xs)
`;

val binarySearchLoopFuel_def = Define `
  (binarySearchLoopFuel
      (a : int list) (key : int)
      (lo : num) (hi : num) 0 =
     lo) /\
  (binarySearchLoopFuel
      a key lo hi (SUC fuel) =
     if lo < hi then
       let mid = (lo + hi) DIV 2 in
         if BinarySearch_nthD mid a < key then
           binarySearchLoopFuel a key (mid + 1) hi fuel
         else
           binarySearchLoopFuel a key lo mid fuel
     else
       lo)
`;

val binarySearchLoop_def = new_definition (
  "binarySearchLoop_def",
  ``binarySearchLoop
      (a : int list) (key : int)
      (lo : num) (hi : num) =
      binarySearchLoopFuel a key lo hi (hi - lo)``
);

val BinarySearch_def = new_definition (
  "BinarySearch_def",
  ``BinarySearch (a : int list) (key : int) =
      binarySearchLoop a key 0 (LENGTH a)``
);

val BinarySearch_postcond_def = new_definition (
  "BinarySearch_postcond_def",
  ``BinarySearch_postcond
      (a : int list) (key : int) (result : num) <=>
      result <= LENGTH a /\
      EVERY (\x : int. x < key) (TAKE result a) /\
      EVERY (\x : int. key <= x) (DROP result a)``
);

val BinarySearch_spec_satisfied =
  ``!(a : int list) (key : int).
      BinarySearch_precond a key ==>
      BinarySearch_postcond a key (BinarySearch a key)``;
