(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2005_a5:
  evaluation of the definite integral from zero to one of
  ln(x + 1) / (x^2 + 1) as pi times ln 2 divided by 8.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory transcTheory integrationTheory;

val putnam_2005_a5 =
  ``integration$integral (interval [0, 1])
      (\x : real. ln (x + 1) / (x pow 2 + 1)) =
    pi * ln 2 / 8``;
