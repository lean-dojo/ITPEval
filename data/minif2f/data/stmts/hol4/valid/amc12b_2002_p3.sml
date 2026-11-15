(*
  Statement-only formalization of miniF2F valid problem amc12b_2002_p3: primality of a
  quadratic natural-number expression forces its positive input to equal 3. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val amc12b_2002_p3 =
  ``!n : num.
      0 < n /\
      prime (n EXP 2 + 2 - 3 * n)
      ==>
      n = 3``;
