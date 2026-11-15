(*
  Statement-only formalization of miniF2F test problem aime_1984_p1. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory ratTheory;

val aime_1984_p1 =
  ``!u : num -> rat.
      (!n. u (n + 1) = u n + 1q) /\
      (ITSET (\k acc. u (k + 1) + acc) (count 98) 0q = 137q)
      ==>
      (ITSET (\k acc. u (2 * (k + 1)) + acc) (count 49) 0q = 93q)``;
