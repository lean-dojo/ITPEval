(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1988_a1:
  the planar Lebesgue measure of the region satisfying
  |x| - |y| <= 1 and |y| <= 1 is six. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory pred_setTheory realTheory;
open extrealTheory measureTheory lebesgue_measureTheory martingaleTheory;

val putnam_1988_a1 =
  ``!(R : (real # real) set).
      R =
        {p : real # real |
          abs (FST p) - abs (SND p) <= 1 /\
          abs (SND p) <= 1}
      ==>
      measure (prod_measure_space lebesgue lebesgue) R = Normal 6``;
