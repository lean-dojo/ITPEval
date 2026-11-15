(*
  Statement-only formalization of VERINA corpus artifact verina_basic_37,
  catalog title "findFirstOccurrence": the executable scan of a nondecreasing
  integer array returns the first index containing the target, or -1 when the
  target is absent. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val findFirstOccurrence_pairwise_def = Define `
  (findFirstOccurrence_pairwise ([] : int list) = T) /\
  (findFirstOccurrence_pairwise (x::xs) =
     (EVERY (\y : int. x <= y) xs /\
      findFirstOccurrence_pairwise xs))
`;

val findFirstOccurrence_precond_def = new_definition (
  "findFirstOccurrence_precond_def",
  ``findFirstOccurrence_precond
      (arr : int list) (target : int) <=>
      findFirstOccurrence_pairwise arr``
);

val findFirstOccurrence_loop_def = Define `
  (findFirstOccurrence_loop
      (target : int) ([] : int list) (index : num) =
     (~1 : int)) /\
  (findFirstOccurrence_loop
      target (a::rest) index =
     if a = target then
       int_of_num index
     else if target < a then
       (~1 : int)
     else
       findFirstOccurrence_loop target rest (index + 1))
`;

val findFirstOccurrence_def = new_definition (
  "findFirstOccurrence_def",
  ``findFirstOccurrence
      (arr : int list) (target : int) =
      findFirstOccurrence_loop target arr 0``
);

val findFirstOccurrence_postcond_def = new_definition (
  "findFirstOccurrence_postcond_def",
  ``findFirstOccurrence_postcond
      (arr : int list) (target : int) (result : int) <=>
      (result = (~1 : int) \/ 0 <= result) /\
      (0 <= result ==>
        Num result < LENGTH arr /\
        EL (Num result) arr = target /\
        (!i : num. i < Num result ==> EL i arr <> target)) /\
      (result = (~1 : int) ==>
        (!i : num. i < LENGTH arr ==> EL i arr <> target))``
);

val findFirstOccurrence_spec_satisfied =
  ``!(arr : int list) (target : int).
      findFirstOccurrence_precond arr target ==>
      findFirstOccurrence_postcond
        arr target (findFirstOccurrence arr target)``;
