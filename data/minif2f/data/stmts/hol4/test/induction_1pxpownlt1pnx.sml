(*
  Statement-only formalization of miniF2F test problem induction_1pxpownlt1pnx. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val induction_1pxpownlt1pnx =
  ``!x : real. !n : num.
      ~1 < x /\ 0 < n
      ==>
      1 + &n * x <= (1 + x) pow n``;
