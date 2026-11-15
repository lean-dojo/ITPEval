(*
  Statement-only formalization of miniF2F valid problem
  numbertheory_2dvd4expn: 2 divides 4^n for every nonzero natural number n.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val numbertheory_2dvd4expn =
  ``!n : num. ~(n = 0) ==> divides 2 (4 EXP n)``;
