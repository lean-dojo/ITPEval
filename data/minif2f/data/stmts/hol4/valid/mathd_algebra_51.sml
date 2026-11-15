(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_51: positive real numbers
  with a fixed sum and ratio have a determined difference. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_51 =
  ``!a b : real.
      0 < a /\ 0 < b /\
      a + b = 35 /\
      a = (2 / 5) * b
      ==>
      b - a = 15``;
