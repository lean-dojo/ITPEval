(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2005_b1:
  the explicit nonzero bivariate real polynomial (y-2x)(y-2x-1) vanishes at
  (floor a, floor (2a)) for every real a. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pairTheory pred_setTheory realTheory
     intrealTheory real_sigmaTheory;

val putnam_2005_b1 =
  ``let P =
      \ij : num # num.
        if ij = (0, 1) then (~1 : real)
        else if ij = (0, 2) then 1
        else if ij = (1, 0) then 2
        else if ij = (1, 1) then ~4
        else if ij = (2, 0) then 4
        else 0
    in
    let support =
      \P : num # num -> real.
        {ij : num # num | P ij <> 0}
    in
    let polynomial =
      \P : num # num -> real.
        FINITE (support P)
    in
    let eval =
      \P : num # num -> real.
      \x y : real.
        REAL_SUM_IMAGE
          (\ij : num # num.
             P ij * x pow (FST ij) * y pow (SND ij))
          (support P)
    in
      polynomial P /\
      (?ij : num # num. P ij <> 0) /\
      !a : real.
        eval P
          (real_of_int (INT_FLOOR a))
          (real_of_int (INT_FLOOR (2 * a))) =
        0``;
