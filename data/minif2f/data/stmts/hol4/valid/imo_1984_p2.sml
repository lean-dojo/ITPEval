(*
  Statement-only formalization of miniF2F valid artifact imo_1984_p2: divisibility conditions
  on positive natural numbers forcing their sum to be at least 19. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val imo_1984_p2 =
  ``!a b : num.
      0 < a /\ 0 < b /\
      ~(divides 7 a) /\
      ~(divides 7 b) /\
      ~(divides 7 (a + b)) /\
      divides (7 EXP 7) ((a + b) EXP 7 - a EXP 7 - b EXP 7)
      ==>
      19 <= a + b``;
