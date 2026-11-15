(*
  Statement-only formalization of miniF2F valid problem algebra_apb4leq8ta4pb4: a quartic
  inequality for two positive real numbers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val algebra_apb4leq8ta4pb4 =
  ``!a b : real.
      0 < a /\ 0 < b
      ==>
      (a + b) pow 4 <= 8 * (a pow 4 + b pow 4)``;
