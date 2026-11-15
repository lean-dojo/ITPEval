(*
  Statement-only formalization of the Logipedia corpus artifact nat.minus_le
  (catalog title "nat.minus_le"): truncated subtraction of one natural number
  from another is at most the original natural number. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_minus_le =
  ``!(x : num) (y : num). x - y <= x``;
