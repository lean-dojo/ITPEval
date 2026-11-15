(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1982_b2:
  evaluation of a Gaussian-weighted integral of the number of integer lattice
  points in a centered disk as pi times the square of a theta-series
  expression. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pairTheory pred_setTheory realTheory
     intrealTheory seqTheory transcTheory extrealTheory measureTheory;
open lebesgueTheory lebesgue_measureTheory;

val putnam_1982_b2 =
  ``let A =
      \x : real.
      \y : real.
        CARD
          {mn : int # int |
             real_of_int (FST mn) pow 2 +
                 real_of_int (SND mn) pow 2 <=
               x pow 2 + y pow 2}
    in
    let g =
      suminf
        (\k : num.
           exp (-((&k : real) pow 2)))
    in
    let I =
      lebesgue$integral lebesgue
        (\x : real.
           lebesgue$integral lebesgue
             (\y : real.
                Normal
                  (&(A x y) *
                   exp (-(x pow 2) - y pow 2))))
    in
      I = Normal (pi * (2 * g - 1) pow 2)``;
