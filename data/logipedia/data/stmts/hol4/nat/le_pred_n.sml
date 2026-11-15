(*
  Statement-only formalization of the Logipedia corpus artifact nat.le_pred_n
  (catalog title "nat.le_pred_n"): the predecessor of every natural number is
  less than or equal to that number. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_le_pred_n =
  ``!n : num. PRE n <= n``;
