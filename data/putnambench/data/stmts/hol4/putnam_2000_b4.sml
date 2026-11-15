(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2000_b4:
  every continuous real function satisfying the quadratic functional equation
  f(2x^2 - 1) = 2x f(x) vanishes on the closed interval [-1, 1]. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_topologyTheory;

val putnam_2000_b4 =
  ``!f : real -> real.
      f continuous_on UNIV /\
      (!x : real. f (2 * x pow 2 - 1) = 2 * x * f x)
      ==>
      !x : real.
        -1 <= x /\ x <= 1
        ==>
        f x = 0``;
