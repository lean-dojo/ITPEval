(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_144: positive natural
  numbers in arithmetic progression with sum 60 and a strict triangle inequality have common
  difference less than 10. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_algebra_144 =
  ``!a b c d : num.
      0 < a /\
      0 < b /\
      0 < c /\
      0 < d /\
      c - b = d /\
      b - a = d /\
      a + b + c = 60 /\
      c < a + b
      ==>
      d < 10``;
