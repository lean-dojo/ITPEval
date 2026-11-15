(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2012_b5:
  bounded real functions with values at least one admit a representation of
  their real-power supremum by an attained affine maximum. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory transcTheory;

val putnam_2012_b5 =
  ``!(g1 g2 : real -> real).
      (!x : real. 1 <= g1 x /\ 1 <= g2 x) /\
      (?B1 B2 : real.
         !x : real. g1 x <= B1 /\ g2 x <= B2)
      ==>
      ?h1 h2 : real -> real.
        !x : real.
          ?t0 : real.
            sup (IMAGE (\s : real. g1 s powr x * g2 s) UNIV) =
              x * h1 t0 + h2 t0 /\
            !t : real.
              x * h1 t + h2 t <= x * h1 t0 + h2 t0``;
