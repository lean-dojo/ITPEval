(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1990_b2:
  a real series built from the stated finite-product coefficients has sum
  negative one when |x| < 1 and |z| > 1. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;
open real_topologyTheory;

val putnam_1990_b2 =
  ``!x z : real. !P : num -> real.
      abs x < 1 /\
      1 < abs z /\
      (!j : num.
         1 <= j
         ==>
         P j =
           REAL_PROD_IMAGE
             (\i : num. 1 - z * x pow i)
             (count j) /
           REAL_PROD_IMAGE
             (\i : num. z - x pow i)
             (IMAGE SUC (count j)))
      ==>
      ((\n : num.
          1 +
          SIGMA
            (\j : num. (1 + x pow j) * P j)
            (IMAGE SUC (count n))) -->
        0)
      sequentially``;
