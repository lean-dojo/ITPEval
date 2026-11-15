(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_227. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val mathd_numbertheory_227 =
  ``!x y n : num.
      0 < x /\ 0 < y /\ 0 < n /\
      ((&x : real) / 4 + (&y : real) / 6 =
       (&(x + y) : real) / (&n : real))
      ==>
      n = 5``;
