(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_126: identifying
  the least positive natural number satisfying prescribed GCD and LCM equations with 40.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory;

val mathd_numbertheory_126 =
  ``!x a : num.
      0 < x /\
      0 < a /\
      gcd a 40 = x + 3 /\
      lcm a 40 = x * (x + 3) /\
      (!b : num.
         0 < b /\
         gcd b 40 = x + 3 /\
         lcm b 40 = x * (x + 3)
         ==>
         a <= b)
      ==>
      a = 8``;
