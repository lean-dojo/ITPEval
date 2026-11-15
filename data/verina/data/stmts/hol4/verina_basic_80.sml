(*
  Statement-only formalization of VERINA corpus artifact verina_basic_80,
  catalog title "only_once": the executable Boolean program scans an integer
  array while counting occurrences of a key and returns true exactly when the
  key occurs once, under its unrestricted precondition and correctness
  contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val only_once_precond_def = new_definition (
  "only_once_precond_def",
  ``only_once_precond (a : int list) (key : int) <=> T``
);

val only_once_loopFuel_def = Define `
  (only_once_loopFuel
      0
      (a : 'a list)
      (key : 'a)
      (i : num)
      (keyCount : num) =
     (keyCount = 1)) /\
  (only_once_loopFuel
      (SUC fuel)
      a
      key
      i
      keyCount =
     if i < LENGTH a then
       let newCount =
         if EL i a = key then keyCount + 1 else keyCount
       in
         only_once_loopFuel fuel a key (i + 1) newCount
     else
       (keyCount = 1))
`;

val only_once_loop_def = new_definition (
  "only_once_loop_def",
  ``only_once_loop
      (a : 'a list)
      (key : 'a)
      (i : num)
      (keyCount : num) =
      only_once_loopFuel (LENGTH a - i) a key i keyCount``
);

val only_once_def = new_definition (
  "only_once_def",
  ``only_once (a : int list) (key : int) =
      only_once_loop a key 0 0``
);

val count_occurrences_def = new_definition (
  "count_occurrences_def",
  ``count_occurrences (a : 'a list) (key : 'a) =
      FOLDL
        (\count x.
          if x = key then count + 1 else count)
        0
        a``
);

val only_once_postcond_def = new_definition (
  "only_once_postcond_def",
  ``only_once_postcond
      (a : int list) (key : int) (result : bool) <=>
      (count_occurrences a key = 1 ==> result) /\
      (count_occurrences a key <> 1 ==> ~result)``
);

val only_once_spec_satisfied =
  ``!(a : int list) (key : int).
      only_once_precond a key ==>
      only_once_postcond a key (only_once a key)``;
