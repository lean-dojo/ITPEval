(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_541:
  natural numbers greater than one whose product is 2005 have sum 406. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_541 =
  ``!m n : num.
      1 < m /\
      1 < n /\
      m * n = 2005
      ==>
      m + n = 406``;
