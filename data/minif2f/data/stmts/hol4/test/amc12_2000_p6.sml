(*
  Statement-only formalization of miniF2F test problem amc12_2000_p6: a bounded-prime
  product-minus-sum disequality. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val amc12_2000_p6 =
  ``!p q : num.
      prime p /\ prime q /\
      (4 <= p /\ p <= 18) /\
      (4 <= q /\ q <= 18)
      ==>
      ~(p * q - (p + q) = 194)``;
