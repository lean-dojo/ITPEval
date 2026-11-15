(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q505798, "Lagrange's theorem (group theory)": the natural cardinality of a
  subgroup divides the natural cardinality of its ambient group, including
  the total-cardinality convention for infinite carriers. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open dividesTheory groupTheory pred_setTheory;

val q505798_nat_card_def = new_definition(
  "q505798_nat_card_def",
  ``q505798_nat_card (s : 'a set) =
      if FINITE s then CARD s else 0``);

val card_subgroup_dvd_card =
  ``!(g : 'a group) (s : 'a group).
      Subgroup s g ==>
      q505798_nat_card s.carrier divides q505798_nat_card g.carrier``;
