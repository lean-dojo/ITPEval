(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1986_a2:
  the units digit of the integer part of 10^20000 divided by 10^100 + 3 is
  3. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val putnam_1986_a2 =
  ``((((10 : num) EXP 20000) DIV (10 EXP 100 + 3)) MOD 10 = 3)``;
