(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_521:
  determining an even natural number from its difference and product with another
  even natural number. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_521 =
  ``!m n : num.
      EVEN m /\
      EVEN n /\
      m - n = 2 /\
      m * n = 288
      ==>
      m = 18``;
