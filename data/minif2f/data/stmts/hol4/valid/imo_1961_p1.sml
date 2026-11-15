(*
  Statement-only formalization of miniF2F valid artifact imo_1961_p1: algebraic inequalities
  relating the sum and sum of squares of three positive, pairwise-distinct real numbers under
  a multiplicative constraint. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val imo_1961_p1 =
  ``!x y z a b : real.
      0 < x /\ 0 < y /\ 0 < z /\
      x <> y /\ y <> z /\ z <> x /\
      x + y + z = a /\
      x pow 2 + y pow 2 + z pow 2 = b pow 2 /\
      x * y = z pow 2
      ==>
      0 < a /\ b pow 2 < a pow 2 /\ a pow 2 < 3 * b pow 2``;
