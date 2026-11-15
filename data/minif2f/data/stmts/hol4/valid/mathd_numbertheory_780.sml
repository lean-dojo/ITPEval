(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_780. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory;

val mathd_numbertheory_780 =
  ``!m x : int.
      0 <= x /\
      10 <= m /\
      m <= 99 /\
      (6 * x) % m = 1 /\
      (x - 6 ** 2) % m = 0
      ==>
      m = 43``;
