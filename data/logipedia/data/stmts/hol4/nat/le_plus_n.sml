(*
  Statement-only formalization of the Logipedia corpus artifact nat.le_plus_n
  (catalog title "nat.le_plus_n"): every natural number m is less than or
  equal to n plus m. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_le_plus_n =
  ``!(n : num) (m : num). m <= n + m``;
