(*
  Statement-only formalization of Logipedia corpus artifact cong.mod_times
  (catalog title "cong.mod_times"): reducing a product of natural numbers
  modulo a positive modulus equals reducing the product of the individually
  reduced factors modulo that modulus. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val cong_mod_times =
  ``!n m p : num.
      0 < p
      ==>
      (n * m) MOD p =
      ((n MOD p) * (m MOD p)) MOD p``;
