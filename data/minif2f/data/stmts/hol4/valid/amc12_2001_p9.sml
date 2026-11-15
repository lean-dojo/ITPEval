(*
  Statement-only formalization of miniF2F valid problem amc12_2001_p9: a real functional
  equation on positive inputs, with f(500) = 3, determining f(600). This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val amc12_2001_p9 =
  ``!f : real -> real.
      (!x y : real.
         0 < x /\ 0 < y
         ==>
         f (x * y) = f x / y) /\
      f 500 = 3
      ==>
      f 600 = 5 / 2``;
