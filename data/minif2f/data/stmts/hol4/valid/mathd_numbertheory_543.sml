(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_543:
  the natural-number divisor count of 30^4, minus 2, is 123. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory;

val mathd_numbertheory_543 =
  ``CARD {d : num | divides d (30 EXP 4)} - 2 = 123``;
