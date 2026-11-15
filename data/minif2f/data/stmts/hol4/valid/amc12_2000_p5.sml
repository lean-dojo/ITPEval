(*
  Statement-only formalization of miniF2F valid problem amc12_2000_p5: a real
  absolute-value relation below 2 implying a linear identity. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val amc12_2000_p5 =
  ``!x p : real.
      x < 2 /\
      abs (x - 2) = p
      ==>
      x - p = 2 - 2 * p``;
