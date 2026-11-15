(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2015_a3:
  the base-2 principal complex logarithm of the double product of
  1 + exp(2*pi*i*a*b/2015), for 1 <= a,b <= 2015, equals 13725.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory transcTheory complexTheory;

val putnam_2015_a3 =
  ``let indices = IMAGE SUC (count 2015) in
    let principal_arg =
      \z : complex.
        if z = 0 then 0
        else if arg z <= pi then arg z else arg z - 2 * pi
    in
    let complex_log =
      \z : complex.
        (ln (modu z), principal_arg z)
    in
      complex_log
        (ITSET
           (\a outer.
              ITSET
                (\b inner.
                   (1 +
                    complex_exp
                      (i * (2 * pi * &a * &b / 2015))) *
                   inner)
                indices
                1 *
              outer)
           indices
           1) /
      complex_log 2 =
      (13725 : complex)``;
