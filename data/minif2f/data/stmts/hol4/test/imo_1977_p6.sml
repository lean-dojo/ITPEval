(*
  Statement-only formalization of miniF2F test problem imo_1977_p6. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val imo_1977_p6 =
  ``!f : num -> num.
      (!n. 0 < f n) /\
      (!n. 0 < n ==> f (f n) < f (n + 1))
      ==>
      !n. 0 < n ==> f n = n``;
