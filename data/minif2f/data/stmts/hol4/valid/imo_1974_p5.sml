(*
  Statement-only formalization of miniF2F valid problem imo_1974_p5. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val imo_1974_p5 =
  ``!a b c d s : real.
      0 < a /\
      0 < b /\
      0 < c /\
      0 < d /\
      s =
        a / (a + b + d) +
        b / (a + b + c) +
        c / (b + c + d) +
        d / (a + c + d)
      ==>
      1 < s /\ s < 2``;
