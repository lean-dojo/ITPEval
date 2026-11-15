(*
  Statement-only formalization of miniF2F test problem
  numbertheory_2pownm1prime_nprime: if 2^n - 1 is prime for a positive natural
  number n, then n is prime. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val numbertheory_2pownm1prime_nprime =
  ``!n : num.
      0 < n /\
      prime (2 EXP n - 1)
      ==>
      prime n``;
