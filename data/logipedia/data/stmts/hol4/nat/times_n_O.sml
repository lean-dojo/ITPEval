(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.times_n_O (catalog title "nat.times_n_O"): zero equals every natural
  number multiplied by zero. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_times_n_O =
  ``!n : num. 0 = n * 0``;
