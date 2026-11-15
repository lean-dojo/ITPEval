(*
  Statement-only formalization of miniF2F valid problem amc12b_2002_p6: a polynomial identity
  over the reals determines its two nonzero coefficients. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val amc12b_2002_p6 =
  ``!a b : real.
      a <> 0 /\
      b <> 0 /\
      (!x : real.
         x pow 2 + a * x + b = (x - a) * (x - b))
      ==>
      a = 1 /\ b = -2``;
