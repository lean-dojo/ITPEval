(*
  Statement-only formalization of miniF2F test problem induction_12dvd4expnp1p20:
  divisibility of 4^(n+1) + 20 by 12 for every natural number n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val induction_12dvd4expnp1p20 =
  ``!n : num. divides 12 (4 EXP (n + 1) + 20)``;
