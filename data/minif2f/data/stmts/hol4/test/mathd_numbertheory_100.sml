(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_100:
  determining a positive natural number from its greatest common divisor and least common
  multiple with 40. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory;

val _ = new_theory "hello";

val mathd_numbertheory_100 =
  ``!n : num.
      0 < n /\
      gcd n 40 = 10 /\
      lcm n 40 = 280
      ==>
      n = 70``;

val _ = export_theory();
