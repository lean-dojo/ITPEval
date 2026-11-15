(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2004_b4:
  composing equal-angle counterclockwise rotations about the consecutive
  real-axis points 1 through n translates every complex point by n.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory transcTheory complexTheory;

val putnam_2004_b4 =
  ``!n : num.
      !R Rk : num -> complex -> complex.
        2 <= n /\
        R 0 = (\z : complex. z) /\
        (!k : num.
           R (k + 1) =
             (\z : complex. Rk (k + 1) (R k z))) /\
        Rk =
          (\k : num.
           \Q : complex.
             complex_of_real (&k) +
             complex_exp (i * (2 * pi / &n)) *
               (Q - complex_of_real (&k)))
        ==>
        R n = (\z : complex. z + complex_of_real (&n))``;
