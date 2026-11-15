(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_64:
  39 is the least natural number x such that 30 * x is congruent to 42 modulo
  47. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_64 =
  ``(30 * 39) MOD 47 = 42 /\
    (!x : num. (30 * x) MOD 47 = 42 ==> 39 <= x)``;
