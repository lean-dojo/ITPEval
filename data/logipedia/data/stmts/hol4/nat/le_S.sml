(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.le_S (catalog title "nat.le_S"): if one natural number is at most
  another, it is also at most that number's successor. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_le_S =
  ``!(n : num) (m : num).
      n <= m ==> n <= SUC m``;
