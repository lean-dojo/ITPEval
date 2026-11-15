(*
  Statement-only formalization of "Pi is Transcendental" from Hundred Theorems item 053. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pred_setTheory realTheory intrealTheory real_sigmaTheory
     transcTheory;

val pi_is_transcendental =
  ``!p : num -> int.
      FINITE {n | p n <> 0} /\
      (?n. p n <> 0)
      ==>
      SIGMA (\n. real_of_int (p n) * pi pow n) {n | p n <> 0} <> 0``;
