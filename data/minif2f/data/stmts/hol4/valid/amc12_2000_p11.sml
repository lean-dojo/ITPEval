(*
  Statement-only formalization of miniF2F valid problem amc12_2000_p11: a real-algebra
  identity for two nonzero variables satisfying a product-difference equation. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val amc12_2000_p11 =
  ``!a b : real.
      ~(a = 0) /\ ~(b = 0) /\
      a * b = a - b
      ==>
      a / b + b / a - a * b = 2``;
