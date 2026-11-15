(*
  Statement-only formalization of VERINA artifact verina_advanced_39,
  cataloged as "maxOfList": the executable recursive program returns a
  greatest element of a non-empty list of natural numbers. This file contains
  no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory;

val maxOfList_precond_def = new_definition (
  "maxOfList_precond_def",
  ``maxOfList_precond (lst : num list) <=>
      LENGTH lst > 0``
);

val maxOfList_helper_def = Define `
  (maxOfList_helper ([] : num list) = 0) /\
  (maxOfList_helper [x] = x) /\
  (maxOfList_helper (x::y::ys) =
     let maxTail = maxOfList_helper (y::ys)
     in
       if x > maxTail then x else maxTail)
`;

val maxOfList_def = new_definition (
  "maxOfList_def",
  ``maxOfList (lst : num list) =
      maxOfList_helper lst``
);

val maxOfList_postcond_def = new_definition (
  "maxOfList_postcond_def",
  ``maxOfList_postcond
      (lst : num list) (result : num) <=>
      MEM result lst /\
      !x : num. MEM x lst ==> x <= result``
);

val maxOfList_spec_satisfied =
  ``!lst : num list.
      maxOfList_precond lst ==>
      maxOfList_postcond lst (maxOfList lst)``;
