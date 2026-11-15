(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2001_b5:
  a continuous real function satisfying the stated linear self-composition
  equation is scalar multiplication. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_topologyTheory;

val putnam_2001_b5 =
  ``!a b : real. !g : real -> real.
      0 < a /\ a < 1 / 2 /\
      0 < b /\ b < 1 / 2 /\
      g continuous_on UNIV /\
      (!x : real. g (g x) = a * g x + b * x)
      ==>
      ?c : real. !x : real. g x = c * x``;
