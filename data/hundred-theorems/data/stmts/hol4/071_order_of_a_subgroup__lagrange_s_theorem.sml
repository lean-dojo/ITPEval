(*
  Statement-only formalization of "Order of a Subgroup (Lagrange's Theorem)"
  from Hundred Theorems artifact 071. Every subgroup of a finite group has
  carrier cardinality dividing the carrier cardinality of the group. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open dividesTheory groupTheory pred_setTheory;

val order_of_a_subgroup_lagrange_s_theorem =
  ``!(g : 'a group) (h : 'a group).
      Subgroup h g /\ FINITE g.carrier ==>
      (CARD h.carrier) divides (CARD g.carrier)``;
