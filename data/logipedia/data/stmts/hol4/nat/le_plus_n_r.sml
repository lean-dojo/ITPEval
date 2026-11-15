(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.le_plus_n_r (catalog title "nat.le_plus_n_r"): every natural number m
  is less than or equal to m plus any natural number n. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_le_plus_n_r =
  ``!(n : num) (m : num). m <= m + n``;
