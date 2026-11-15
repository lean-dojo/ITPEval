(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_457:
  divisibility of a positive natural number's factorial by 80325 forces the
  number to be at least 17. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val mathd_numbertheory_457 =
  ``!n : num.
      0 < n /\
      divides 80325 (FACT n)
      ==>
      17 <= n``;
