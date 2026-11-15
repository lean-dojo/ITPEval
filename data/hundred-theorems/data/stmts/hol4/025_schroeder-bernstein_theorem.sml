(*
  Statement-only formalization of "Schroeder-Bernstein Theorem" from Hundred Theorems item 025.
  This file contains no proof.
*)

(*
  Hundred Theorems item 025, "Schroeder-Bernstein Theorem": injections between two sets in both
  directions imply that the sets are in bijection. This is a statement-only formalization and
  contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory;

val schroeder_bernstein_theorem =
  ``!(A : 'a set) (B : 'b set)
     (f : 'a -> 'b) (g : 'b -> 'a).
      INJ f A B /\ INJ g B A ==>
      ?h : 'a -> 'b. BIJ h A B``;
