(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_435:
  a positive natural number satisfying three universal coprimality conditions
  involving consecutive residues modulo 6 is at least 5. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory;

val mathd_numbertheory_435 =
  ``!k : num.
      0 < k /\
      (!n : num. gcd (6 * n + k) (6 * n + 3) = 1) /\
      (!n : num. gcd (6 * n + k) (6 * n + 2) = 1) /\
      (!n : num. gcd (6 * n + k) (6 * n + 1) = 1)
      ==>
      5 <= k``;
