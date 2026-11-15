(*
  Statement-only formalization of miniF2F valid problem imo_1990_p3: a divisibility condition
  on 2^n + 1 forcing the natural number n to equal 3. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val imo_1990_p3 =
  ``!n : num.
      2 <= n /\
      divides (n EXP 2) (2 EXP n + 1)
      ==>
      n = 3``;
