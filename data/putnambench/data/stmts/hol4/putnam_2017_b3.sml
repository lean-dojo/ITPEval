(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2017_b3:
  a real power series with coefficients in {0,1} that equals 3/2 at 2/3
  has an irrational value at 1/2. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_of_ratTheory seqTheory;

val putnam_2017_b3 =
  ``!c : num -> real.
      (!n : num. c n = 0 \/ c n = 1) /\
      suminf
        (\n : num. c n * ((2 : real) / 3) pow n) =
      3 / 2
      ==>
      suminf
        (\n : num. c n * ((1 : real) / 2) pow n)
      NOTIN q_set``;
