(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q5463860 (thousand-theorems__hol4__Q5463860), "Focal subgroup theorem":
  for a finite-index Sylow p-subgroup of an arbitrary group, its intersection
  with the ambient commutator subgroup is its focal subgroup. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val q5463860_group_def = new_definition (
  "q5463860_group_def",
  ``q5463860_group
      (mul : 'a -> 'a -> 'a) (e : 'a) (ginv : 'a -> 'a) <=>
      (!x y z. mul (mul x y) z = mul x (mul y z)) /\
      (!x. mul e x = x) /\
      (!x. mul x e = x) /\
      (!x. mul (ginv x) x = e) /\
      (!x. mul x (ginv x) = e)``);

val q5463860_subgroup_def = new_definition (
  "q5463860_subgroup_def",
  ``q5463860_subgroup
      (mul : 'a -> 'a -> 'a) (e : 'a) (ginv : 'a -> 'a)
      (H : 'a set) <=>
      e IN H /\
      (!x y. x IN H /\ y IN H ==> mul x y IN H) /\
      (!x. x IN H ==> ginv x IN H)``);

val q5463860_generated_subgroup_def = new_definition (
  "q5463860_generated_subgroup_def",
  ``q5463860_generated_subgroup
      (mul : 'a -> 'a -> 'a) (e : 'a) (ginv : 'a -> 'a)
      (gens : 'a set) =
      {x |
        !H : 'a set.
          q5463860_subgroup mul e ginv H /\
          gens SUBSET H
          ==>
          x IN H}``);

val q5463860_pow_def = new_definition (
  "q5463860_pow_def",
  ``q5463860_pow
      (mul : 'a -> 'a -> 'a) (e : 'a) (x : 'a) (n : num) =
      FUNPOW (\y. mul x y) n e``);

val q5463860_p_subgroup_def = new_definition (
  "q5463860_p_subgroup_def",
  ``q5463860_p_subgroup
      (p : num)
      (mul : 'a -> 'a -> 'a) (e : 'a) (ginv : 'a -> 'a)
      (P : 'a set) <=>
      q5463860_subgroup mul e ginv P /\
      !x.
        x IN P ==>
        ?k : num. q5463860_pow mul e x (p ** k) = e``);

val q5463860_sylow_def = new_definition (
  "q5463860_sylow_def",
  ``q5463860_sylow
      (p : num)
      (mul : 'a -> 'a -> 'a) (e : 'a) (ginv : 'a -> 'a)
      (P : 'a set) <=>
      q5463860_p_subgroup p mul e ginv P /\
      !Q : 'a set.
        q5463860_p_subgroup p mul e ginv Q /\
        P SUBSET Q
        ==>
        Q = P``);

val q5463860_finite_index_def = new_definition (
  "q5463860_finite_index_def",
  ``q5463860_finite_index
      (mul : 'a -> 'a -> 'a) (P : 'a set) <=>
      FINITE (IMAGE (\g. IMAGE (\h. mul g h) P) UNIV)``);

val q5463860_commutator_element_def = new_definition (
  "q5463860_commutator_element_def",
  ``q5463860_commutator_element
      (mul : 'a -> 'a -> 'a) (ginv : 'a -> 'a) (x : 'a) (u : 'a) =
      mul (mul (mul x u) (ginv x)) (ginv u)``);

val q5463860_commutator_subgroup_def = new_definition (
  "q5463860_commutator_subgroup_def",
  ``q5463860_commutator_subgroup
      (mul : 'a -> 'a -> 'a) (e : 'a) (ginv : 'a -> 'a) =
      q5463860_generated_subgroup mul e ginv
        {g | ?x u. g = q5463860_commutator_element mul ginv x u}``);

val q5463860_focal_subgroup_def = new_definition (
  "q5463860_focal_subgroup_def",
  ``q5463860_focal_subgroup
      (mul : 'a -> 'a -> 'a) (e : 'a) (ginv : 'a -> 'a)
      (P : 'a set) =
      q5463860_generated_subgroup mul e ginv
        {g |
          g IN P /\
          ?x u.
            x IN P /\
            g = q5463860_commutator_element mul ginv x u}``);

val focal_subgroup_theorem =
  ``!(mul : 'a -> 'a -> 'a) (e : 'a) (ginv : 'a -> 'a)
      (p : num) (P : 'a set).
      q5463860_group mul e ginv /\
      prime p /\
      q5463860_sylow p mul e ginv P /\
      q5463860_finite_index mul P
      ==>
      q5463860_commutator_subgroup mul e ginv INTER P =
      q5463860_focal_subgroup mul e ginv P``;
