(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.minus_O_n (catalog title "nat.minus_O_n"): subtracting any natural
  number from zero yields zero. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_minus_O_n =
  ``!n : num. 0 = 0 - n``;
