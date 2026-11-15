(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_405:
  a natural-number Fibonacci recurrence at inputs congruent to 5, 10, and 15
  modulo 16 has a sum with remainder 5 modulo 7. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_405 =
  ``!a b c : num. !t : num -> num.
      (t 0 = 0 /\
       t 1 = 1 /\
       (!n : num.
          n > 1 ==>
          t n = t (n - 2) + t (n - 1)) /\
       a MOD 16 = 5 /\
       b MOD 16 = 10 /\
       c MOD 16 = 15)
      ==>
      (t a + t b + t c) MOD 7 = 5``;
