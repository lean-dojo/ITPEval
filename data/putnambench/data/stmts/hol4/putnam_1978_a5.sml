(*
  Statement-only formalization of PutnamBench artifact putnam_1978_a5:
  the product inequality comparing sinc values of finitely many reals in
  the open interval from zero to pi with the sinc of their arithmetic mean.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory transcTheory;

val putnam_1978_a5 =
  ``!n : num. !a : num -> real. !mu : real.
      0 < n /\
      (!i : num. i < n ==> 0 < a i /\ a i < pi) /\
      mu = SIGMA (\i : num. a i / &n) (count n)
      ==>
      real_sigma$product
        (count n)
        (\i : num. sin (a i) / a i) <=
      (sin mu / mu) pow n``;
