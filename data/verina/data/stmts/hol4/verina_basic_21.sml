(*
  Statement-only formalization of VERINA corpus artifact verina_basic_21,
  catalog title "isSublist": the executable Boolean program scans an integer
  list for the first list as a contiguous slice and satisfies the exact
  existence-of-a-slice correctness contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val isSublist_precond_def = new_definition (
  "isSublist_precond_def",
  ``isSublist_precond
      (sub : int list) (main : int list) <=>
      T``
);

val isSublist_check_def = Define `
  (isSublist_check
      (sub : int list)
      ([] : int list) =
     if LENGTH sub > 0 then F else T) /\
  (isSublist_check
      sub
      (x::xs) =
     if LENGTH sub > LENGTH (x::xs) then
       F
     else if sub = TAKE (LENGTH sub) (x::xs) then
       T
     else
       isSublist_check sub xs)
`;

val isSublist_def = new_definition (
  "isSublist_def",
  ``isSublist
      (sub : int list) (main : int list) =
      if LENGTH sub > LENGTH main then
        F
      else
        isSublist_check sub main``
);

val isSublist_postcond_def = new_definition (
  "isSublist_postcond_def",
  ``isSublist_postcond
      (sub : int list)
      (main : int list)
      (result : bool) <=>
      ((?i : num.
          i + LENGTH sub <= LENGTH main /\
          sub = TAKE (LENGTH sub) (DROP i main)) <=>
       result)``
);

val isSublist_spec_satisfied =
  ``!(sub : int list) (main : int list).
      isSublist_precond sub main ==>
      isSublist_postcond sub main (isSublist sub main)``;
