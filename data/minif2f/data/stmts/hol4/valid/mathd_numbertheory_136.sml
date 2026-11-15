(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_136:
  solving a linear equation over the natural numbers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_136 =
  ``!n : num.
      123 * n + 17 = 39500
      ==>
      n = 321``;
