(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.le_n_O_elim (catalog title "nat.le_n_O_elim"): if a natural number is
  less than or equal to zero, every predicate true at zero is true at that
  number. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_le_n_O_elim =
  ``!(n : num).
      n <= 0 ==> !(P : num -> bool). P 0 ==> P n``;
