(*
  Statement-only formalization of PutnamBench artifact putnam_1971_b3:
  the Lebesgue measure of the real times at which one natural floor count is
  twice a delayed natural floor count is one. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pred_setTheory realTheory intrealTheory;
open extrealTheory measureTheory lebesgue_measureTheory;

val putnam_1971_b3 =
  ``!T : real.
      0 < T
      ==>
      measure lebesgue
        {t : real |
          T <= t /\
          INT_FLOOR t = 2 * INT_FLOOR (t - T)} =
        Normal 1``;
