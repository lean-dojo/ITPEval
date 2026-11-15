(*
  Statement-only formalization of "The Area of a Circle" from Hundred Theorems item 009. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory pred_setTheory realTheory transcTheory;
open extrealTheory measureTheory lebesgue_measureTheory martingaleTheory;

val area_of_a_circle =
  ``!(c : real # real) (r : real).
      0 <= r ==>
      measure (prod_measure_space lebesgue lebesgue)
        {p : real # real |
          (FST p - FST c) pow 2 + (SND p - SND c) pow 2 < r pow 2} =
      Normal (pi * r pow 2)``;
