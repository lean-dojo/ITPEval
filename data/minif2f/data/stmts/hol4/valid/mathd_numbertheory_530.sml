(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_530:
  positive natural numbers whose real ratio lies strictly between 5 and 6 have
  lcm-to-gcd quotient at least 22. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory realTheory;

val mathd_numbertheory_530 =
  ``!n k : num.
      0 < n /\
      0 < k /\
      (&n : real) / (&k : real) < 6 /\
      (5 : real) < (&n : real) / (&k : real)
      ==>
      22 <= lcm n k DIV gcd n k``;
