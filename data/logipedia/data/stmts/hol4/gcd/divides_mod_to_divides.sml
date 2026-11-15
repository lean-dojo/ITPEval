(*
  Statement-only formalization of the Logipedia corpus artifact
  gcd.divides_mod_to_divides (catalog title "gcd.divides_mod_to_divides"):
  for all natural numbers p, m, and n with n positive, if p divides the
  remainder of m modulo n and p divides n, then p divides m. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val gcd_divides_mod_to_divides =
  ``!(p : num) (m : num) (n : num).
      0 < n ==>
      divides p (m MOD n) ==>
      divides p n ==>
      divides p m``;
