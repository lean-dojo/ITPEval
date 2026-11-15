(*
  Statement-only formalization of miniF2F valid problem amc12a_2013_p7: a real-valued sequence
  satisfying the Fibonacci recurrence, with two specified terms determining an earlier term.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val amc12a_2013_p7 =
  ``!s : num -> real.
      (!n : num. s (n + 2) = s (n + 1) + s n) /\
      s 9 = 110 /\
      s 7 = 42
      ==>
      s 4 = 10``;
