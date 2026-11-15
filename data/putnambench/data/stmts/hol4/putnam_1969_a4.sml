(*
  Statement-only formalization of PutnamBench artifact putnam_1969_a4:
  convergence of the alternating series with terms n^(-n) to the definite
  integral of x^x on the unit interval. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory seqTheory
     transcTheory integrationTheory;

val putnam_1969_a4 =
  ``((\n : num.
       SIGMA
         (\i : num.
            (-1 : real) pow (i + 1) / (&i : real) pow i)
         (IMAGE SUC (count n))) -->
     integration$integral (interval [0, 1])
       (\x : real. x powr x))
    sequentially``;
