(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2010_a6:
  divergence of the improper integral formed from a strictly decreasing
  continuous real function on the nonnegative reals that tends to zero.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_topologyTheory limTheory integrationTheory;

val putnam_2010_a6 =
  ``!f : real -> real.
      (!x y : real.
         0 <= x /\ 0 <= y /\ x < y
         ==>
         f y < f x) /\
      f continuous_on {x : real | 0 <= x} /\
      (f --> 0) at_posinfinity
      ==>
      ~(?L : real.
          ((\z : real.
              integration$integral (interval [0, z])
                (\x : real. (f x - f (x + 1)) / f x)) --> L)
            at_posinfinity)``;
