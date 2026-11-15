(*
  Statement-only formalization of miniF2F test problem aime_1999_p11: a reduced positive
  rational angle whose tangent is a finite sine sum, determining the sum of its numerator
  and denominator. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory pred_setTheory realTheory real_sigmaTheory
     transcTheory;

val aime_1999_p11 =
  ``!m : num. !n : num.
      0 < m /\
      0 < n /\
      gcd m n = 1 /\
      sum {1 .. 35} (\k. sin (5 * &k * pi / 180)) =
        tan ((&m / &n) * pi / 180) /\
      m < 90 * n
      ==>
      m + n = 177``;
