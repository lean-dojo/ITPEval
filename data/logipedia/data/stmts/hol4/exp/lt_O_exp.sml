(*
  Statement-only formalization of the Logipedia corpus artifact exp.lt_O_exp
  (catalog title "exp.lt_O_exp"): every positive natural number has a positive
  natural power for every natural exponent. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val lt_O_exp =
  ``!n m : num. 0 < n ==> 0 < n EXP m``;
