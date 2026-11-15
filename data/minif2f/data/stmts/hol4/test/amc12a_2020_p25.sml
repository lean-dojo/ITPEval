(*
  Statement-only formalization of miniF2F test problem amc12a_2020_p25: the finite real
  solution set of a floor-function equation has sum 420, determining the sum of the reduced
  numerator and denominator of its rational coefficient. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pred_setTheory realTheory intrealTheory real_sigmaTheory
     ratTheory real_of_ratTheory;

val amc12a_2020_p25 =
  ``!a : rat. !S : real set.
      (!x.
         x IN S <=>
         real_of_int (INT_FLOOR x) *
             (x - real_of_int (INT_FLOOR x)) =
           real_of_rat a * x pow 2) /\
      FINITE S /\
      SIGMA (\x. x) S = 420
      ==>
      &(RATD a) + RATN a = 929``;
