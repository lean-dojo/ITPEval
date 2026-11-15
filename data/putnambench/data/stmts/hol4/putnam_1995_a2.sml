(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1995_a2:
  characterization of the positive real pairs for which the given improper
  integral involving nested square roots converges. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory transcTheory integrationTheory;

val putnam_1995_a2 =
  ``!a b : real.
      0 < a /\ 0 < b
      ==>
      ((?limit : real.
          !e : real.
            0 < e
            ==>
            ?T : real.
              !t : real.
                T <= t
                ==>
                abs
                  (integration$integral (interval [b, t])
                     (\x : real.
                        sqrt (sqrt (x + a) - sqrt x) -
                        sqrt (sqrt x - sqrt (x - b))) -
                   limit) < e)
       <=>
       a = b)``;
