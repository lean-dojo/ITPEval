(*
  Statement-only formalization of miniF2F test problem imo_1959_p1: the coprimality of
  two linear expressions in a positive natural number. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory;

val imo_1959_p1 =
  ``!n : num.
      0 < n ==>
      gcd (21 * n + 4) (14 * n + 3) = 1``;
