(*
  Statement-only formalization of the Logipedia corpus artifact
  div_mod.lt_mod_m_m (catalog title "div_mod.lt_mod_m_m"): for all natural
  numbers n and positive moduli m, the remainder of n modulo m is less than m.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val div_mod_lt_mod_m_m =
  ``!n m : num.
      0 < m
      ==>
      n MOD m < m``;
