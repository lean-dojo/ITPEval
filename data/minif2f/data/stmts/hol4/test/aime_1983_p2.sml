(*
  Statement-only formalization of miniF2F test problem aime_1983_p2: a lower bound for a sum
  of three real absolute-value terms on the interval from p to 15. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val aime_1983_p2 =
  ``!x p : real. !f : real -> real.
      (0 < p /\ p < 15) /\
      (p <= x /\ x <= 15) /\
      (f x = abs (x - p) + abs (x - 15) + abs (x - p - 15))
      ==>
      15 <= f x``;
