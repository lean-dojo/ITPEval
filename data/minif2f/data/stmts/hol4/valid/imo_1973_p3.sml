(*
  Statement-only formalization of miniF2F valid problem imo_1973_p3: a lower bound on
  a squared coefficient sum when x^4 + a*x^3 + b*x^2 + a*x + 1 has a real root.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val imo_1973_p3 =
  ``!a b : real.
      (?x : real.
         x pow 4 + a * x pow 3 + b * x pow 2 + a * x + 1 = 0)
      ==>
      (4 : real) / 5 <= a pow 2 + b pow 2``;
