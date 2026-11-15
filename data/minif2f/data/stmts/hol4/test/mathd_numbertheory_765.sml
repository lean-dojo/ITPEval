(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_765:
  a negative integer whose product with 24 has remainder 15 modulo 1199 is at
  most -449. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory;

val mathd_numbertheory_765 =
  ``!x : int.
      x < 0 /\
      (24 * x) % 1199 = 15
      ==>
      x <= -449``;
