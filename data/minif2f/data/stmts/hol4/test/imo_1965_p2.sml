(*
  Statement-only formalization of miniF2F test problem imo_1965_p2: a sign-constrained
  homogeneous system of three real linear equations whose only solution is zero. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val imo_1965_p2 =
  ``!x y z : real. !a : num -> real.
      0 < a 0 /\ 0 < a 4 /\ 0 < a 8 /\
      a 1 < 0 /\ a 2 < 0 /\
      a 3 < 0 /\ a 5 < 0 /\
      a 6 < 0 /\ a 7 < 0 /\
      0 < a 0 + a 1 + a 2 /\
      0 < a 3 + a 4 + a 5 /\
      0 < a 6 + a 7 + a 8 /\
      a 0 * x + a 1 * y + a 2 * z = 0 /\
      a 3 * x + a 4 * y + a 5 * z = 0 /\
      a 6 * x + a 7 * y + a 8 * z = 0
      ==>
      x = 0 /\ y = 0 /\ z = 0``;
