(*
  Statement-only formalization of miniF2F test problem
  numbertheory_3pow2pownm1mod2pownp3eq2pownp2: for every positive natural
  number n, 3 raised to 2^n minus 1 has remainder 2^(n+2) modulo 2^(n+3).
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val numbertheory_3pow2pownm1mod2pownp3eq2pownp2 =
  ``!n : num.
      0 < n ==>
      (3 EXP (2 EXP n) - 1) MOD (2 EXP (n + 3)) =
      2 EXP (n + 2)``;
