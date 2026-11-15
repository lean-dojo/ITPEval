(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  thousand-theorems__hol4__Q550402, "Dirichlet's theorem on arithmetic
  progressions": for every nonzero natural modulus and every invertible
  residue class, the set of primes in that residue class is infinite. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val q550402_dirichlet_s_theorem_on_arithmetic_progressions =
  ``!q a : num.
      q <> 0 /\
      (?b : num. (a * b) MOD q = 1 MOD q)
      ==>
      INFINITE {p : num | prime p /\ p MOD q = a MOD q}``;
