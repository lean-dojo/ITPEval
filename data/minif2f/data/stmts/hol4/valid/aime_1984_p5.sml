(*
  Statement-only formalization of miniF2F valid problem aime_1984_p5. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val aime_1984_p5 =
  ``!a b : real.
      0 < a /\ 0 < b /\
      (ln a / ln 8 + ln (b pow 2) / ln 4 = 5) /\
      (ln b / ln 8 + ln (a pow 2) / ln 4 = 7)
      ==>
      a * b = 512``;
