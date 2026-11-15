(*
  Statement-only formalization of PutnamBench artifact putnam_1971_b6:
  the sum of each positive integer's greatest odd divisor divided by that
  integer differs from two thirds of the endpoint by less than one.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory;
open realTheory real_sigmaTheory;

val putnam_1971_b6 =
  ``!delta : num -> num.
      (!n : num.
         0 < n
         ==>
         ODD (delta n) /\
         divides (delta n) n /\
         (!t : num.
            ODD t /\ divides t n
            ==>
            t <= delta n))
      ==>
      !x : num.
        0 < x
        ==>
        abs
          (SIGMA
             (\i : num. &(delta (i + 1)) / &(i + 1))
             (count x) -
           2 * &x / 3) < 1``;
