(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_79,
  catalog title "twoSum": the executable nested left-to-right search returns
  the lexicographically first increasing pair of indices whose integer values
  sum to the target, or NONE when no such pair exists. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory optionTheory pairTheory;

val twoSum_nthD_def = Define `
  (twoSum_nthD
      (index : num) ([] : int list) = (0 : int)) /\
  (twoSum_nthD
      0 (x::xs) = x) /\
  (twoSum_nthD
      (SUC index) (x::xs) =
     twoSum_nthD index xs)
`;

val twoSum_precond_def = new_definition (
  "twoSum_precond_def",
  ``twoSum_precond
      (nums : int list) (target : int) <=>
      T``
);

val twoSum_inner_def = Define `
  (twoSum_inner
      (x : int)
      ([] : int list)
      (target : int)
      (j : num) =
     (NONE : num option)) /\
  (twoSum_inner
      x
      (y::ys)
      target
      j =
     if x + y = target then
       SOME j
     else
       twoSum_inner x ys target (j + 1))
`;

val twoSum_outer_def = Define `
  (twoSum_outer
      ([] : int list)
      (target : int)
      (i : num) =
     (NONE : (num # num) option)) /\
  (twoSum_outer
      (x::xs)
      target
      i =
     case twoSum_inner x xs target (i + 1) of
       NONE => twoSum_outer xs target (i + 1)
     | SOME j => SOME (i,j))
`;

val twoSum_def = new_definition (
  "twoSum_def",
  ``twoSum
      (nums : int list) (target : int) =
      twoSum_outer nums target 0``
);

val twoSum_pairwiseNoSum_def = Define `
  (twoSum_pairwiseNoSum
      (target : int) ([] : int list) <=>
     T) /\
  (twoSum_pairwiseNoSum
      target (x::xs) <=>
     EVERY (\y : int. x + y <> target) xs /\
     twoSum_pairwiseNoSum target xs)
`;

val twoSum_noEarlierOuter_def = new_definition (
  "twoSum_noEarlierOuter_def",
  ``twoSum_noEarlierOuter
      (nums : int list) (target : int) (i : num) <=>
      !i' k.
        i' < i /\ i' < k /\ k < LENGTH nums ==>
        twoSum_nthD i' nums + twoSum_nthD k nums <> target``
);

val twoSum_noEarlierInner_def = new_definition (
  "twoSum_noEarlierInner_def",
  ``twoSum_noEarlierInner
      (nums : int list) (target : int) (i : num) (j : num) <=>
      !k.
        i < k /\ k < j ==>
        twoSum_nthD i nums + twoSum_nthD k nums <> target``
);

val twoSum_postcond_def = new_definition (
  "twoSum_postcond_def",
  ``twoSum_postcond
      (nums : int list)
      (target : int)
      (result : (num # num) option) <=>
      case result of
        NONE => twoSum_pairwiseNoSum target nums
      | SOME pair =>
          let i = FST pair in
          let j = SND pair in
            i < j /\
            j < LENGTH nums /\
            twoSum_nthD i nums + twoSum_nthD j nums = target /\
            twoSum_noEarlierOuter nums target i /\
            twoSum_noEarlierInner nums target i j``
);

val twoSum_spec_satisfied =
  ``!(nums : int list) (target : int).
      twoSum_precond nums target ==>
      twoSum_postcond
        nums target (twoSum nums target)``;
