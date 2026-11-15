(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q2226800, "Schur–Zassenhaus theorem": a normal subgroup whose natural
  cardinality is coprime to its index has a subgroup complement, so every
  group element has a unique factorization with the complement factor first.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory groupTheory pred_setTheory;

val q2226800_nat_card_def = new_definition(
  "q2226800_nat_card_def",
  ``q2226800_nat_card (s : 'a set) =
      if FINITE s then CARD s else 0``);

val q2226800_index_def = new_definition(
  "q2226800_index_def",
  ``q2226800_index (g : 'a group) (n : 'a group) =
      q2226800_nat_card (CosetPartition g n)``);

val q2226800_is_left_complement_def = new_definition(
  "q2226800_is_left_complement_def",
  ``q2226800_is_left_complement
      (g : 'a group) (h : 'a group) (n : 'a group) <=>
      Subgroup h g /\
      Subgroup n g /\
      BIJ
        (\p. g.op (FST p) (SND p))
        (h.carrier CROSS n.carrier)
        g.carrier``);

val Subgroup_exists_left_complement_of_coprime =
  ``!(g : 'a group) (n : 'a group).
      Group g /\
      normal_subgroup n g /\
      gcd
        (q2226800_nat_card n.carrier)
        (q2226800_index g n) = 1
      ==>
      ?h : 'a group.
        q2226800_is_left_complement g h n``;
