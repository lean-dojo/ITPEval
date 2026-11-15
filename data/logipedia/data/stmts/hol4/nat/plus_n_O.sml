(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.plus_n_O (catalog title "nat.plus_n_O"): every natural number equals
  that number plus zero. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_plus_n_O =
  ``!n : num. n = n + 0``;
