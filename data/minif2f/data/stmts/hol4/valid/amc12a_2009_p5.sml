(*
  Statement-only formalization of miniF2F valid problem amc12a_2009_p5: a real cubic equation
  implies that the cube of the variable is 125. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val amc12a_2009_p5 =
  ``!x : real.
      x pow 3 - (x + 1) * (x - 1) * x = 5
      ==>
      x pow 3 = 125``;
