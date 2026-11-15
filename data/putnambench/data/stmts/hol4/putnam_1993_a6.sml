(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1993_a6:
  a self-describing sequence of twos and threes has a real floor-sequence
  characterization of the positions of its twos. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory realTheory intrealTheory;

val putnam_1993_a6 =
  ``!seq : num -> num.
      (!n : num. seq n = 2 \/ seq n = 3) /\
      (!n : num.
         seq n = 2 <=>
         ?N : num. n = SIGMA (\i : num. seq i + 1) (count N))
      ==>
      ?r : real.
        !n : num.
          seq n = 2 <=>
          ?m : num.
            int_of_num (n + 1) =
            1 + INT_FLOOR (r * (&m : real))``;
