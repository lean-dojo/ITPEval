(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_155. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val mathd_numbertheory_155 =
  ``CARD {x : num | 100 <= x /\ x <= 999 /\ x MOD 19 = 7} = 48``;
