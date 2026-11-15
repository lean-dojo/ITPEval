(*
  Statement-only formalization of miniF2F test problem
  algebra_bleqa_apbon2msqrtableqambsqon8b: for positive real numbers a and b with b at most a,
  the arithmetic-geometric mean gap is bounded by (a - b)^2 / (8 * b). This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val algebra_bleqa_apbon2msqrtableqambsqon8b =
  ``!a b : real.
      0 < a /\ 0 < b /\ b <= a
      ==>
      (a + b) / 2 - sqrt (a * b) <= (a - b) pow 2 / (8 * b)``;
