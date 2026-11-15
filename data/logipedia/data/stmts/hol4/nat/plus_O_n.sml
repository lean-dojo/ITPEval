(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.plus_O_n (catalog title "nat.plus_O_n"): every natural number equals
  zero plus that number. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_plus_O_n =
  ``!n : num. n = 0 + n``;
