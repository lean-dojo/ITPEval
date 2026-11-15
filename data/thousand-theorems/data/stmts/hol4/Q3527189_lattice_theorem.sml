(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q3527189, "Lattice theorem": Noether's third isomorphism theorem for groups,
  stating that for normal subgroups N contained in M, the quotient of G/N by
  the image of M is isomorphic to G/M. This file contains no proof.
*)

open HolKernel Parse boolLib;
open groupTheory pred_setTheory;

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
          (quotient_group g m) /\
        !x. x IN g.carrier ==>
          e
            (left_coset
              (quotient_group g n)
              (homo_image
                (left_coset g n.carrier)
                m
                (quotient_group g n)).carrier
              (left_coset g n.carrier x)) =
          left_coset g m.carrier x``;
