(*
  Statement-only formalization of the Logipedia corpus artifact nat.le_plus_b
  (catalog title "nat.le_plus_b"): if n plus a natural number b is at most m,
  then n is at most m. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_le_plus_b =
  ``!(b : num) (n : num) (m : num).
      n + b <= m ==> n <= m``;
