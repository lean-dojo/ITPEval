(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1187646, "Fundamental theorem on homomorphisms": for every group
  homomorphism, the quotient of its domain by its kernel is isomorphic to its
  image. This file contains no proof.
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
          (homo_image f g h) /\
        !x. x IN g.carrier ==>
            e (left_coset g (kernel f g h) x) = f x``;
