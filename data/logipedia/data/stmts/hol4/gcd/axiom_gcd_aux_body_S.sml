(*
  Statement-only formalization of the Logipedia corpus artifact
  gcd.axiom_gcd_aux_body_S (catalog title "gcd.axiom_gcd_aux_body_S"):
  for every natural-number index, gcd_aux_body at the successor index equals
  the curried function that returns n when n divides m according to the
  source modulo test, and otherwise returns gcd_aux p n (m mod n). This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_gcd_auxiliary_type =
  numSyntax.num -->
  numSyntax.num -->
  numSyntax.num -->
  numSyntax.num;

val _ = new_constant (
  "logipedia_gcd_gcd_aux",
  logipedia_gcd_auxiliary_type);

val _ = new_constant (
  "logipedia_gcd_gcd_aux_body",
  logipedia_gcd_auxiliary_type);

val gcd_axiom_gcd_aux_body_S =
  ``!p : num.
      logipedia_gcd_gcd_aux_body (SUC p) =
      (\(m : num) (n : num).
         if m MOD n = 0 then
           n
         else
           logipedia_gcd_gcd_aux p n (m MOD n))``;
