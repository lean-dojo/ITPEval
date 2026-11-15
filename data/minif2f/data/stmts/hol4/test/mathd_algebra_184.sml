(*
  Statement-only formalization of miniF2F test problem mathd_algebra_184: positive real
  solutions of two quadratic equations determine a square-root value. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_184 =
  ``!a b : real.
      0 < a /\ 0 < b /\
      a pow 2 = 6 * b /\
      a pow 2 = 54 / b
      ==>
      a = 3 * sqrt 2``;
