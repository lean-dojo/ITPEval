(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_31. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory seqTheory;

val mathd_algebra_31 =
  ``!x : real. !u : num -> real.
      0 <= x /\
      (!n. 0 <= u n) /\
      (!n. u (n + 1) = sqrt (x + u n)) /\
      (u --> 9)
      ==>
      9 = sqrt (x + 9)``;
