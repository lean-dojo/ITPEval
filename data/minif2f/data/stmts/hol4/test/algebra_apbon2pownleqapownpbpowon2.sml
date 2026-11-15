(*
  Statement-only formalization of miniF2F test problem
  algebra_apbon2pownleqapownpbpowon2: an inequality comparing the nth power of the arithmetic
  mean of two positive reals with the arithmetic mean of their nth powers. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val algebra_apbon2pownleqapownpbpowon2 =
  ``!a b : real. !n : num.
      0 < a /\ 0 < b /\ 0 < n
      ==>
      ((a + b) / 2) pow n <= (a pow n + b pow n) / 2``;
