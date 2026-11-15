(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1997_a3:
  the improper integral of the product of two specified real power series
  equals the square root of exp 1. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_topologyTheory seqTheory;
open transcTheory integrationTheory;

val putnam_1997_a3 =
  ``let even_factorial =
      \n : num. (2 : real) pow n * &(FACT n)
    in
    let series1 =
      \x : real.
        suminf
          (\n : num.
             (~1 : real) pow n * x pow (2 * n + 1) /
             even_factorial n)
    in
    let series2 =
      \x : real.
        suminf
          (\n : num.
             x pow (2 * n) / (even_factorial n) pow 2)
    in
      ((\t : real.
          integration$integral (interval [0, t])
            (\x : real. series1 x * series2 x)) -->
        sqrt (exp 1))
        at_posinfinity``;
