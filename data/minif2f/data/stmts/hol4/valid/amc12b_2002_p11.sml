(*
  Statement-only formalization of miniF2F valid problem amc12b_2002_p11: primality of a
  natural-number expression under four primality assumptions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val amc12b_2002_p11 =
  ``!a b : num.
      prime a /\
      prime b /\
      prime (a + b) /\
      prime (a - b)
      ==>
      prime (a + b + (a - b + (a + b)))``;
