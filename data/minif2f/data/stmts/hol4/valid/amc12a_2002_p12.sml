(*
  Statement-only formalization of miniF2F valid problem amc12a_2002_p12: a real quadratic with
  two distinct prime natural roots has constant term 122. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory realTheory;

val amc12a_2002_p12 =
  ``!f : real -> real. !k : real. !a b : num.
      (!x : real. f x = x pow 2 - 63 * x + k) /\
      f (&a) = 0 /\
      f (&b) = 0 /\
      ~(a = b) /\
      prime a /\
      prime b
      ==>
      k = 122``;
