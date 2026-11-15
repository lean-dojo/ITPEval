(*
  Statement-only formalization of miniF2F artifact mathd_algebra_421: paired quadratic
  identities and strict ordering determine that two real inputs differ by 6. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_421 =
  ``!a b c d : real.
      b = a pow 2 + 4 * a + 6 /\
      b = (1 / 2) * a pow 2 + a + 6 /\
      d = c pow 2 + 4 * c + 6 /\
      d = (1 / 2) * c pow 2 + c + 6 /\
      a < c
      ==>
      c - a = 6``;
