(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_35:
  evaluating p(x) = 2 - x^2 at q(2), where q(x) = 6/x for nonzero x.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_35 =
  ``!p q : real -> real.
      (!x : real. p x = 2 - x pow 2) /\
      (!x : real. x <> 0 ==> q x = 6 / x)
      ==>
      p (q 2) = -7``;
