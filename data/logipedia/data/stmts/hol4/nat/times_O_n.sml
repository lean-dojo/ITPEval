(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.times_O_n (catalog title "nat.times_O_n"): zero equals zero multiplied
  by every natural number. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_times_O_n =
  ``!n : num. 0 = 0 * n``;
