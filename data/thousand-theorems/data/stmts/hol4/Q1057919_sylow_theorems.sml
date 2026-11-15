(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1057919, "Sylow theorems": existence of subgroups of prime-power order,
  conjugacy of Sylow subgroups, divisibility of their index by their count,
  and congruence of that count to one modulo the prime. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory groupTheory pred_setTheory;

val q1057919_nat_card_def = new_definition(
  "q1057919_nat_card_def",
  ``q1057919_nat_card (s : 'a set) =
      if FINITE s then CARD s else 0``);

val q1057919_is_p_group_def = new_definition(
  "q1057919_is_p_group_def",
  ``q1057919_is_p_group (p : num) (h : 'a group) <=>
      !x : 'a.
        x IN h.carrier
        ==>
        ?k : num. h.exp x (p ** k) = h.id``);

val q1057919_is_sylow_def = new_definition(
  "q1057919_is_sylow_def",
  ``q1057919_is_sylow (p : num) (g : 'a group) (h : 'a group) <=>
      Subgroup h g /\
      q1057919_is_p_group p h /\
      !q : 'a group.
        Subgroup q g /\
        q1057919_is_p_group p q /\
        h.carrier SUBSET q.carrier
        ==>
        q.carrier = h.carrier``);

val q1057919_sylow_carriers_def = new_definition(
  "q1057919_sylow_carriers_def",
  ``q1057919_sylow_carriers (p : num) (g : 'a group) =
      {s : 'a set |
        ?h : 'a group.
          q1057919_is_sylow p g h /\ s = h.carrier}``);

val Sylow_exists_subgroup_card_pow_prime =
  ``!(g : 'a group) (p : num) (n : num).
      Group g /\
      FINITE g.carrier /\
      prime p /\
      (p ** n) divides q1057919_nat_card g.carrier
      ==>
      ?h : 'a group.
        Subgroup h g /\
        q1057919_nat_card h.carrier = p ** n``;

val Sylow_isPretransitive_of_finite =
  ``!(g : 'a group) (p : num).
      Group g /\
      prime p /\
      FINITE (q1057919_sylow_carriers p g)
      ==>
      !(P : 'a group) (Q : 'a group).
        q1057919_is_sylow p g P /\
        q1057919_is_sylow p g Q
        ==>
        ?a : 'a.
          a IN g.carrier /\
          (conjugate_subgroup P g a).carrier = Q.carrier``;

val Sylow_card_dvd_index =
  ``!(g : 'a group) (p : num) (P : 'a group).
      Group g /\
      prime p /\
      FINITE (q1057919_sylow_carriers p g) /\
      q1057919_is_sylow p g P
      ==>
      q1057919_nat_card (q1057919_sylow_carriers p g)
        divides
      q1057919_nat_card (CosetPartition g P)``;

val card_sylow_modEq_one =
  ``!(g : 'a group) (p : num).
      Group g /\
      prime p /\
      FINITE (q1057919_sylow_carriers p g)
      ==>
      q1057919_nat_card (q1057919_sylow_carriers p g) MOD p =
      1 MOD p``;
