(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1065966, "Isomorphism theorem": the first, second, and third isomorphism
  theorems for groups, expressed using kernels, homomorphic images, subgroup
  intersections and products, and quotient groups. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open groupTheory pred_setTheory;

val quotientKerEquivRange =
  ``!(g : 'a group) (h : 'b group) (f : 'a -> 'b).
      Group g /\
      Group h /\
      GroupHomo f g h
      ==>
      ?e : 'a set -> 'b.
        GroupIso e
          (quotient_group g (kernel_group f g h))
          (homo_image f g h)``;

val quotientInfEquivProdNormalQuotient =
  ``!(g : 'a group) (h : 'a group) (n : 'a group).
      Group g /\
      Subgroup h g /\
      normal_subgroup n g
      ==>
      ?e : 'a set -> 'a set.
        GroupIso e
          (quotient_group h (monoid_intersect h n))
          (quotient_group (subgroup_cross g h n) n)``;

val quotientQuotientEquivQuotient =
  ``!(g : 'a group) (n : 'a group) (m : 'a group).
      Group g /\
      normal_subgroup n g /\
      normal_subgroup m g /\
      Subgroup n m
      ==>
      ?e : ('a set) set -> 'a set.
        GroupIso e
          (quotient_group
            (quotient_group g n)
            (homo_image
              (left_coset g n.carrier)
              m
              (quotient_group g n)))
          (quotient_group g m)``;
