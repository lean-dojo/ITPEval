(*
  Statement-only formalization of PutnamBench artifact putnam_1977_a4:
  the lacunary real series with terms x^(2^n) / (1 - x^(2^(n+1)))
  equals the rational function x / (1 - x) on (0,1). This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory seqTheory;

val putnam_1977_a4 =
  ``!x : real.
      0 < x /\ x < 1
      ==>
      suminf
        (\n : num.
           x pow (2 EXP n) /
           (1 - x pow (2 EXP (n + 1)))) =
      x / (1 - x)``;
