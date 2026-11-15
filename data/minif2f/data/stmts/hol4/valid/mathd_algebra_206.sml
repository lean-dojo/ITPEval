(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_206: a real quadratic
  with distinct roots 2 * a and b has coefficient sum a + b = -1. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_206 =
  ``!a b : real. !f : real -> real.
      (!x : real. f x = x pow 2 + a * x + b) /\
      2 * a <> b /\
      f (2 * a) = 0 /\
      f b = 0
      ==>
      a + b = -1``;
