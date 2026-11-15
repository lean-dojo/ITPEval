(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2001_b3:
  the infinite series whose terms use the nearest integer to each positive
  integer's square root evaluates to 3. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory realTheory intrealTheory seqTheory
     transcTheory;

val putnam_2001_b3 =
  ``suminf
      (\n : num.
         let nearest =
           real_of_int
             (INT_FLOOR (sqrt (&(n + 1)) + 1 / 2))
         in
           ((2 : real) powr nearest +
            (2 : real) powr (-nearest)) /
           (2 : real) pow (n + 1)) =
    3``;
