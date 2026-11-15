(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2018_b3:
  the positive integers below 10^100 satisfying three simultaneous
  divisibility conditions involving 2^n are exactly 2^2, 2^4, 2^16, and
  2^256. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory;

val putnam_2018_b3 =
  ``{n : num |
       0 < n /\
       n < 10 EXP 100 /\
       divides n (2 EXP n) /\
       divides (n - 1) (2 EXP n - 1) /\
       divides (n - 2) (2 EXP n - 2)} =
    {2 EXP 2; 2 EXP 4; 2 EXP 16; 2 EXP 256}``;
