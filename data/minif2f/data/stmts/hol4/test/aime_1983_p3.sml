(*
  Statement-only formalization of miniF2F test problem aime_1983_p3: the product of the real
  zeros of a function defined using a square root. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;

val aime_1983_p3 =
  ``!f : real -> real.
      (!x.
         f x =
           x pow 2 + 18 * x + 30 -
           2 * (if 0 <= x pow 2 + 18 * x + 45
                then sqrt (x pow 2 + 18 * x + 45)
                else 0)) /\
      FINITE {x | f x = 0}
      ==>
      REAL_PROD_IMAGE (\x. x) {x | f x = 0} = 20``;
