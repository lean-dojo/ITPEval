(*
  Statement-only formalization of Logipedia corpus artifact cong.mod_mod
  (catalog title "cong.mod_mod"): taking the natural-number remainder modulo
  a positive modulus twice gives the same remainder as taking it once. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val cong_mod_mod =
  ``!(n : num) (p : num).
      0 < p
      ==>
      n MOD p = (n MOD p) MOD p``;
