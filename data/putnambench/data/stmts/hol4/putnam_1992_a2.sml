(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1992_a2:
  evaluation of an integral involving the 1992nd Taylor coefficient at zero
  of the real power (1 + x)^alpha. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory limTheory transcTheory;
open integrationTheory real_sigmaTheory;

val putnam_1992_a2 =
  ``let C =
      \alpha : real.
        diffn 1992 (\x : real. (1 + x) powr alpha) 0 / &(FACT 1992)
    in
      integration$integral (interval [0, 1])
        (\y : real.
           C (-y - 1) *
           SIGMA
             (\k : num. 1 / (y + &k))
             (IMAGE SUC (count 1992))) =
      1992``;
