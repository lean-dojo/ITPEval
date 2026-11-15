(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_314:
  a natural-number lower bound from divisibility and modular-remainder hypotheses.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val mathd_numbertheory_314 =
  ``!r n : num.
      r = 1342 MOD 13 /\
      0 < n /\
      divides 1342 n /\
      n MOD 13 < r
      ==>
      6710 <= n``;
