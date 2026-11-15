(*
  Statement-only formalization of VERINA corpus artifact verina_basic_69,
  catalog title "LinearSearch": under the assumption that the target occurs,
  the executable left-to-right search of an integer array returns its first
  target index. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val LinearSearch_nthD_def = Define `
  (LinearSearch_nthD
      ([] : int list) (index : num) = (0 : int)) /\
  (LinearSearch_nthD
      (x::xs) 0 = x) /\
  (LinearSearch_nthD
      (x::xs) (SUC index) =
     LinearSearch_nthD xs index)
`;

val LinearSearch_precond_def = new_definition (
  "LinearSearch_precond_def",
  ``LinearSearch_precond (a : int list) (e : int) <=>
      ?i : num.
        i < LENGTH a /\ LinearSearch_nthD a i = e``
);

val linearSearchAuxFuel_def = Define `
  (linearSearchAuxFuel
      0
      (a : int list)
      (e : int)
      (n : num) =
     0) /\
  (linearSearchAuxFuel
      (SUC fuel)
      a
      e
      n =
     if n < LENGTH a then
       if LinearSearch_nthD a n = e then
         n
       else
         linearSearchAuxFuel fuel a e (n + 1)
     else
       0)
`;

val linearSearchAux_def = new_definition (
  "linearSearchAux_def",
  ``linearSearchAux
      (a : int list) (e : int) (n : num) =
      linearSearchAuxFuel (SUC (LENGTH a - n)) a e n``
);

val LinearSearch_def = new_definition (
  "LinearSearch_def",
  ``LinearSearch (a : int list) (e : int) =
      linearSearchAux a e 0``
);

val LinearSearch_postcond_def = new_definition (
  "LinearSearch_postcond_def",
  ``LinearSearch_postcond
      (a : int list) (e : int) (result : num) <=>
      result < LENGTH a /\
      LinearSearch_nthD a result = e /\
      (!k : num.
         k < result ==>
         LinearSearch_nthD a k <> e)``
);

val LinearSearch_spec_satisfied =
  ``!(a : int list) (e : int).
      LinearSearch_precond a e ==>
      LinearSearch_postcond a e (LinearSearch a e)``;
