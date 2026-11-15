(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2017_b4:
  the logarithmic infinite series with coefficients repeating 3,-1,-1,-1
  evaluates to the square of ln 2. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory seqTheory transcTheory;

val putnam_2017_b4 =
  ``suminf
      (\k : num.
         3 * ln (4 * (&k : real) + 2) / (4 * (&k : real) + 2) -
         ln (4 * (&k : real) + 3) / (4 * (&k : real) + 3) -
         ln (4 * (&k : real) + 4) / (4 * (&k : real) + 4) -
         ln (4 * (&k : real) + 5) / (4 * (&k : real) + 5)) =
    (ln 2) pow 2``;
