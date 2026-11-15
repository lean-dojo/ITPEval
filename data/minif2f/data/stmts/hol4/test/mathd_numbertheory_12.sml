(*
  Statement-only formalization of miniF2F test artifact mathd_numbertheory_12: counting natural
  numbers from 15 through 85 that are divisible by 20. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory;

val mathd_numbertheory_12 =
  ``CARD {x : num | 15 <= x /\ x <= 85 /\ divides 20 x} = 4``;
