(*
  Statement-only formalization of the Logipedia corpus artifact nat.le_n_Sn
  (catalog title "nat.le_n_Sn"): every natural number is less than or equal
  to its successor. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_le_n_Sn =
  ``!n : num. n <= SUC n``;
