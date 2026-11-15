(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.times_n_1 (catalog title "nat.times_n_1"): every natural number equals
  that number multiplied by the successor of zero. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_times_n_1 =
  ``!n : num. n = n * SUC 0``;
