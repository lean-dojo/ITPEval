(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_127: the finite
  sum of powers of two from exponent 0 through 100 has remainder 3 modulo 7. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val mathd_numbertheory_127 =
  ``SIGMA (\k : num. 2 EXP k) (count 101) MOD 7 = 3``;
