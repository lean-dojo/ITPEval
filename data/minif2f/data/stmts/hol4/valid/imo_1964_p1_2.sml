(*
  Statement-only formalization of miniF2F valid problem imo_1964_p1_2: non-divisibility of
  2^n + 1 by 7 for every natural-number exponent n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val imo_1964_p1_2 =
  ``!n : num.
      ~(divides 7 (2 EXP n + 1))``;
