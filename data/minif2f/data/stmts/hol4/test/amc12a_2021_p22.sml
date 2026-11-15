(*
  Statement-only formalization of miniF2F test problem amc12a_2021_p22: a monic real cubic
  with three specified cosine zeros has coefficient product 1 / 32. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val amc12a_2021_p22 =
  ``!a b c : real. !f : real -> real.
      (!x.
         f x = x pow 3 + a * x pow 2 + b * x + c) /\
      (!x.
         f x = 0 <=>
         x = cos (2 * pi / 7) \/
         x = cos (4 * pi / 7) \/
         x = cos (6 * pi / 7))
      ==>
      a * b * c = 1 / 32``;
