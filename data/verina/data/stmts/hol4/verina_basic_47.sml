(*
  Statement-only formalization of VERINA corpus artifact verina_basic_47,
  catalog title "arraySum": the executable integer-array program sums every
  element, and under the nonempty-array precondition its result satisfies the
  recursive prefix-sum postcondition. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val arraySum_precond_def = new_definition (
  "arraySum_precond_def",
  ``arraySum_precond (a : int list) <=>
      0 < LENGTH a``
);

val arraySum_nthD_def = Define `
  (arraySum_nthD
      (index : num) ([] : int list) = (0 : int)) /\
  (arraySum_nthD
      0 (x::xs) = x) /\
  (arraySum_nthD
      (SUC index) (x::xs) =
     arraySum_nthD index xs)
`;

val arraySum_def = Define `
  (arraySum ([] : int list) = (0 : int)) /\
  (arraySum (x::xs) =
     x + arraySum xs)
`;

val sumTo_def = Define `
  (sumTo (a : int list) 0 = (0 : int)) /\
  (sumTo a (SUC n) =
     sumTo a n + arraySum_nthD n a)
`;

val arraySum_postcond_def = new_definition (
  "arraySum_postcond_def",
  ``arraySum_postcond
      (a : int list) (result : int) <=>
      result - sumTo a (LENGTH a) = 0 /\
      sumTo a (LENGTH a) <= result``
);

val arraySum_spec_satisfied =
  ``!a : int list.
      arraySum_precond a ==>
      arraySum_postcond a (arraySum a)``;
