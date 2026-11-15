(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1993_b3:
  the probability that the nearest integer to the ratio of two independent
  uniform points in the open unit interval is even equals 5/4 - pi/4. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory realTheory transcTheory;
open extrealTheory measureTheory lebesgue_measureTheory martingaleTheory;

val putnam_1993_b3 =
  ``measure
      (prod_measure_space lebesgue lebesgue)
      {p : real # real |
        0 < FST p /\ FST p < 1 /\
        0 < SND p /\ SND p < 1 /\
        EVEN (NUM_FLOOR (FST p / SND p + 1 / 2))} =
    Normal (5 / 4 - pi / 4)``;
