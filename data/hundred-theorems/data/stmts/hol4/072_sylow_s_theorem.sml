(*
  Statement-only formalization of "Sylow's Theorem" from Hundred Theorems
  artifact 072. If a prime power divides the order of a finite group, then the
  group has a subgroup whose order is that prime power. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory groupTheory pred_setTheory;

val sylows_theorem =
  ``!(g : 'a group) (p : num) (a : num).
      Group g /\
      FINITE g.carrier /\
      prime p /\
      (p ** a) divides (CARD g.carrier)
      ==>
      ?h : 'a group.
        Subgroup h g /\ CARD h.carrier = p ** a``;
