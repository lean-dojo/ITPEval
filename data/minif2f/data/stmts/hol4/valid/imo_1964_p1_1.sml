(*
  Statement-only formalization of miniF2F valid problem imo_1964_p1_1: divisibility of the
  exponent n when 7 divides 2^n - 1. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val imo_1964_p1_1 =
  ``!n : num.
      divides 7 (2 EXP n - 1)
      ==>
      divides 3 n``;
