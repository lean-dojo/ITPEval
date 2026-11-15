(*
  Statement-only formalization of miniF2F test problem aime_1997_p9: equal fractional parts
  and bounds on a positive real determine a degree-twelve identity. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory intrealTheory;

val aime_1997_p9 =
  ``!a : real.
      0 < a /\
      frac (1 / a) = frac (a pow 2) /\
      2 < a pow 2 /\
      a pow 2 < 3
      ==>
      a pow 12 - 144 * (1 / a) = 233``;
