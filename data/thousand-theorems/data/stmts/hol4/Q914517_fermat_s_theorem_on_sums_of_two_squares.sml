(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q914517, "Fermat's theorem on sums of two squares": every prime natural
  number not congruent to 3 modulo 4 is a sum of two natural-number squares.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val nat_prime_sq_add_sq =
  ``!p : num.
      prime p /\ p MOD 4 <> 3
      ==>
      ?a b : num. a EXP 2 + b EXP 2 = p``;
