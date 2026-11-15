(*
  Statement-only formalization of miniF2F valid problem imo_1979_p1: divisibility of the
  numerator of the alternating harmonic sum through 1/1319. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory realTheory real_sigmaTheory;

val imo_1979_p1 =
  ``!p q : num.
      0 < q /\
      sum {1 .. 1319}
        (\k. (-1 : real) pow (k + 1) * ((1 : real) / (&k : real))) =
        (&p : real) / (&q : real)
      ==>
      divides 1979 p``;
