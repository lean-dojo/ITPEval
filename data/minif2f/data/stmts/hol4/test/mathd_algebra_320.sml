(*
  Statement-only formalization of miniF2F test problem mathd_algebra_320: a
  nonnegative real root of a quadratic, written in normalized radical form
  with positive natural parameters, has parameter sum 26. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val mathd_algebra_320 =
  ``!x : real. !a b c : num.
      0 < a /\ 0 < b /\ 0 < c /\ 0 <= x /\
      2 * x pow 2 = 4 * x + 9 /\
      x = (&a + sqrt (&b)) / &c /\
      c = 2
      ==>
      a + b + c = 26``;
