(*
  Statement-only formalization of the Logipedia corpus artifact
  primes.divides_to_le (catalog title "primes.divides_to_le"): for natural
  numbers n and m, if m is positive and n divides m, then n is at most m.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val primes_divides_to_le =
  ``!(n : num) (m : num).
      0 < m ==>
      divides n m ==>
      n <= m``;
