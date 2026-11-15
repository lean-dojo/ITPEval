(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_3: the sum of the
  first nine positive squares has remainder 5 modulo 10. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val mathd_numbertheory_3 =
  ``SIGMA (\x : num. (x + 1) EXP 2) (count 9) MOD 10 = 5``;
