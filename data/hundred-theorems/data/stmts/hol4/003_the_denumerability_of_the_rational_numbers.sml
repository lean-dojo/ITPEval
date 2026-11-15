(*
  Statement-only formalization of "The Denumerability of the Rational Numbers" from Hundred
  Theorems item 003. This file contains no proof.
*)

open HolKernel Parse boolLib;
open cardinalTheory pred_setTheory ratTheory;

val denumerability_of_the_rational_numbers =
  ``?enumerate : num -> rat.
      BIJ enumerate (UNIV : num set) (UNIV : rat set)``;
