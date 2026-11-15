(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1033910, "Cantor–Bernstein–Schroeder theorem": injections between arbitrary
  sets in both directions imply the existence of a bijection. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory;

val cantor_bernstein_schroeder_theorem =
  ``!a b f g. INJ f a b /\ INJ g b a ==>
      ?h. BIJ h a b``;
