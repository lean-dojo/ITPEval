(*
  Statement-only formalization of "Dirichlet's Theorem" from Hundred Theorems artifact 048.
  For every positive natural modulus and every coprime residue, the set of primes in that
  residue class is infinite. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory gcdTheory pred_setTheory;

val dirichlet_s_theorem =
  ``!d k : num.
      1 <= d /\ coprime k d ==>
      INFINITE {p : num | prime p /\ p MOD d = k MOD d}``;
