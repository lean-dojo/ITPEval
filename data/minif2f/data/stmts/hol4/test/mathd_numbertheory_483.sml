(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_483:
  the Fibonacci-type natural-number recurrence with initial values 1, 1 has
  residue 3 modulo 4 at index 100. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_483 =
  ``!a : num -> num.
      a 1 = 1 /\
      a 2 = 1 /\
      (!n : num. a (n + 2) = a (n + 1) + a n)
      ==>
      a 100 MOD 4 = 3``;
