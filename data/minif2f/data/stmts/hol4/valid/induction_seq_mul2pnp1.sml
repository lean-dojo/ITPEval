(*
  Statement-only formalization of miniF2F valid problem induction_seq_mul2pnp1: the closed
  form of a natural-number sequence defined by u 0 = 0 and
  u (n + 1) = 2 * u n + (n + 1). This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val induction_seq_mul2pnp1 =
  ``!n : num. !u : num -> num.
      u 0 = 0 /\
      (!m : num. u (m + 1) = 2 * u m + (m + 1))
      ==>
      u n = 2 EXP (n + 1) - (n + 2)``;
