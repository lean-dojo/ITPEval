(*
  Statement-only formalization of Hundred Theorems artifact 067, "e is Transcendental":
  Euler's number exp 1 is not a root of any nonzero polynomial with integer
  coefficients. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pred_setTheory realTheory intrealTheory real_sigmaTheory
     transcTheory;

val e_is_transcendental =
  ``!p : num -> int.
      FINITE {n | p n <> 0} /\
      (?n. p n <> 0)
      ==>
      SIGMA (\n. real_of_int (p n) * exp 1 pow n) {n | p n <> 0} <> 0``;
