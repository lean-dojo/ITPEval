(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_764: a modular
  sum of products of inverses of consecutive residues modulo a prime. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory;

val mathd_numbertheory_764 =
  ``!p : num.
      prime p /\
      7 <= p
      ==>
      SIGMA
        (\k : num.
          ((k EXP (p - 2)) MOD p) *
          (((k + 1) EXP (p - 2)) MOD p))
        (IMAGE SUC (count (p - 2))) MOD p = 2``;
