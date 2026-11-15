(*
  Statement-only formalization of the Logipedia corpus artifact nat.pred_Sn
  (catalog title "nat.pred_Sn"): every natural number equals the predecessor
  of its successor. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_pred_Sn =
  ``!n : num. n = PRE (SUC n)``;
