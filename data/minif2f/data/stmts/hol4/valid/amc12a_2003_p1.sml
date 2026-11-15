(*
  Statement-only formalization of miniF2F valid problem amc12a_2003_p1: the difference between
  the sums of 2003 consecutive even and odd natural-number terms is 2003. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val amc12a_2003_p1 =
  ``!u v : num -> num.
      (!n : num. u n = 2 * n + 2) /\
      (!n : num. v n = 2 * n + 1)
      ==>
      SIGMA u (count 2003) - SIGMA v (count 2003) = 2003``;
