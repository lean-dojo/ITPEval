(*
  Statement-only formalization of miniF2F valid problem aime_1988_p4: a real sequence with
  terms of absolute value less than one whose absolute-value sum exceeds the absolute value of
  its sum by 19 must have at least 20 terms. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;

val aime_1988_p4 =
  ``!n : num. !a : num -> real.
      (!k. abs (a k) < 1) /\
      SIGMA (\k. abs (a k)) (count n) =
        19 + abs (SIGMA a (count n))
      ==>
      20 <= n``;
