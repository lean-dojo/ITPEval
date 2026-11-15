(*
  Statement-only formalization of miniF2F test problem induction_pprime_pdvdapowpma: a prime
  natural p divides a^p - a for every positive natural a. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val induction_pprime_pdvdapowpma =
  ``!p a : num.
      0 < a /\ prime p ==>
      divides p (a EXP p - a)``;
