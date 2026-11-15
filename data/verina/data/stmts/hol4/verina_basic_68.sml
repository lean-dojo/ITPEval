(*
  Statement-only formalization of VERINA corpus artifact verina_basic_68,
  catalog title "LinearSearch": the executable left-to-right search of an
  integer array returns the first target index, or the array length when the
  target is absent, under its complete correctness contract. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val LinearSearch_precond_def = new_definition (
  "LinearSearch_precond_def",
  ``LinearSearch_precond (a : int list) (e : int) <=> T``
);

val LinearSearch_nthD_def = Define `
  (LinearSearch_nthD
      ([] : int list) (index : num) = (0 : int)) /\
  (LinearSearch_nthD
      (x::xs) 0 = x) /\
  (LinearSearch_nthD
      (x::xs) (SUC index) =
     LinearSearch_nthD xs index)
`;

val LinearSearch_loopFuel_def = Define `
  (LinearSearch_loopFuel
      0
      (a : int list)
      (e : int)
      (n : num) =
     n) /\
  (LinearSearch_loopFuel
      (SUC fuel)
      a
      e
      n =
     if n < LENGTH a then
       if LinearSearch_nthD a n = e then
         n
       else
         LinearSearch_loopFuel fuel a e (n + 1)
     else
       n)
`;

val LinearSearch_loop_def = new_definition (
  "LinearSearch_loop_def",
  ``LinearSearch_loop
      (a : int list) (e : int) (n : num) =
      LinearSearch_loopFuel (SUC (LENGTH a - n)) a e n``
);

val LinearSearch_def = new_definition (
  "LinearSearch_def",
  ``LinearSearch (a : int list) (e : int) =
      LinearSearch_loop a e 0``
);

val LinearSearch_postcond_def = new_definition (
  "LinearSearch_postcond_def",
  ``LinearSearch_postcond
      (a : int list) (e : int) (result : num) <=>
      result <= LENGTH a /\
      (result = LENGTH a \/ LinearSearch_nthD a result = e) /\
      (!i : num.
         i < result ==>
         LinearSearch_nthD a i <> e)``
);

val LinearSearch_spec_satisfied =
  ``!(a : int list) (e : int).
      LinearSearch_precond a e ==>
      LinearSearch_postcond a e (LinearSearch a e)``;
