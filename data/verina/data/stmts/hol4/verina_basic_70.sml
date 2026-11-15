(*
  Statement-only formalization of VERINA corpus artifact verina_basic_70,
  catalog title "LinearSearch3": under the assumption that an integer array
  contains an element satisfying a predicate, the executable left-to-right
  search returns the first satisfying index. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val LinearSearch3_nthD_def = Define `
  (LinearSearch3_nthD
      ([] : int list) (index : num) = (0 : int)) /\
  (LinearSearch3_nthD
      (x::xs) 0 = x) /\
  (LinearSearch3_nthD
      (x::xs) (SUC index) =
     LinearSearch3_nthD xs index)
`;

val LinearSearch3_precond_def = new_definition (
  "LinearSearch3_precond_def",
  ``LinearSearch3_precond
      (a : int list) (P : int -> bool) <=>
      ?i : num.
        i < LENGTH a /\ P (LinearSearch3_nthD a i)``
);

val LinearSearch3_loopFuel_def = Define `
  (LinearSearch3_loopFuel
      0
      (a : int list)
      (P : int -> bool)
      (n : num) =
     0) /\
  (LinearSearch3_loopFuel
      (SUC fuel)
      a
      P
      n =
     if n < LENGTH a then
       if P (LinearSearch3_nthD a n) then
         n
       else
         LinearSearch3_loopFuel fuel a P (n + 1)
     else
       0)
`;

val LinearSearch3_loop_def = new_definition (
  "LinearSearch3_loop_def",
  ``LinearSearch3_loop
      (a : int list) (P : int -> bool) (n : num) =
      LinearSearch3_loopFuel (SUC (LENGTH a - n)) a P n``
);

val LinearSearch3_def = new_definition (
  "LinearSearch3_def",
  ``LinearSearch3 (a : int list) (P : int -> bool) =
      LinearSearch3_loop a P 0``
);

val LinearSearch3_postcond_def = new_definition (
  "LinearSearch3_postcond_def",
  ``LinearSearch3_postcond
      (a : int list) (P : int -> bool) (result : num) <=>
      result < LENGTH a /\
      P (LinearSearch3_nthD a result) /\
      (!k : num.
         k < result ==>
         ~P (LinearSearch3_nthD a k))``
);

val LinearSearch3_spec_satisfied =
  ``!(a : int list) (P : int -> bool).
      LinearSearch3_precond a P ==>
      LinearSearch3_postcond a P (LinearSearch3 a P)``;
