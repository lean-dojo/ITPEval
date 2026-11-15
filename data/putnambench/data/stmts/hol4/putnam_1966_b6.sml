(*
  Statement-only formalization of PutnamBench artifact putnam_1966_b6:
  every twice-differentiable real solution of y'' + exp(x)y = 0 is eventually
  bounded above and below as x tends to positive infinity. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open realTheory limTheory transcTheory;

val putnam_1966_b6 =
  ``!y : real -> real.
      (!x : real. higher_differentiable 2 y x) /\
      (!x : real. diffn 2 y x + exp x * y x = 0)
      ==>
      ?r s N : real.
        !x : real.
          N < x
          ==>
          r <= y x /\ y x <= s``;
