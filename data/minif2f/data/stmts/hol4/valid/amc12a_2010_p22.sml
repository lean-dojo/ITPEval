(*
  Statement-only formalization of miniF2F valid problem amc12a_2010_p22: a lower bound of 49
  for the sum from k = 1 through 119 of |k * x - 1| for every real x. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;

val amc12a_2010_p22 =
  ``!x : real.
      49 <=
      SIGMA
        (\k : num. abs (&k * x - 1))
        (IMAGE SUC (count 119))``;
