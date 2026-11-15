(*
  Statement-only formalization of miniF2F valid problem
  numbertheory_prmdvsneqnsqmodpeq0: divisibility of an integer by a natural
  prime is equivalent to its square being zero modulo that prime. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory integerTheory;

val numbertheory_prmdvsneqnsqmodpeq0 =
  ``!n : int. !p : num.
      prime p ==>
      ((int_of_num p) int_divides n <=>
       (n ** 2) % (int_of_num p) = 0)``;
