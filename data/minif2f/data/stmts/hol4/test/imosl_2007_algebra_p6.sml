(*
  Statement-only formalization of miniF2F test problem imosl_2007_algebra_p6:
  a strict cyclic cubic inequality for a normalized sequence of 100 nonnegative real numbers.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;

val imosl_2007_algebra_p6 =
  ``!a : num -> real.
      (!n. 0 <= a n) /\
      SIGMA (\x. (a (x + 1)) pow 2) (count 100) = 1
      ==>
      SIGMA
        (\x. (a (x + 1)) pow 2 * a (x + 2))
        (count 99) +
      (a 100) pow 2 * a 1 <
      12 / 25``;
