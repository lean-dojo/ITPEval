(*
  Statement-only formalization of "Divergence of the Harmonic Series" from Hundred Theorems
  item 034. The real harmonic partial sums grow without bound. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;

val divergence_of_the_harmonic_series =
  ``!B : real.
      ?N : num.
        !n : num.
          N <= n
          ==>
          B <=
            SIGMA
              (\i : num. (1 : real) / &(i + 1))
              (count n)``;
