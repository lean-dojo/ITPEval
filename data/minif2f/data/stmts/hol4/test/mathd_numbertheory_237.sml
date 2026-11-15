(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_237:
  the sum of the natural numbers from 0 through 100 has remainder 4 modulo 6.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val _ = new_theory "hello";

val mathd_numbertheory_237 =
  ``SIGMA (\k : num. k) (count 101) MOD 6 = 4``;

val _ = export_theory();
