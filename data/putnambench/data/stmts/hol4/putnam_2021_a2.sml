(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2021_a2:
  the right-hand defining limit for a positive-real function g implies that
  g(x) / x tends to exp 1 as x tends to positive infinity. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_topologyTheory limTheory transcTheory;

val putnam_2021_a2 =
  ``!g : real -> real.
      (!x : real.
         0 < x
         ==>
         ((\r : real.
             ((x + 1) powr (r + 1) - x powr (r + 1)) powr (1 / r)) -->
          g x)
           (at 0 within {r : real | 0 < r}))
      ==>
      ((\x : real. g x / x) --> exp 1) at_posinfinity``;
