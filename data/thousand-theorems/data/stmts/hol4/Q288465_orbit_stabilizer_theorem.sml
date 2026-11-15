(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q288465, "Orbit-stabilizer theorem": for a group acting on a type, the orbit
  of a point is canonically bijective with the left cosets of its stabilizer.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open groupTheory pred_setTheory;

val orbitEquivQuotientStabilizer =
  ``!(g : 'a group) (f : 'a -> 'b -> 'b) (b : 'b).
      Group g /\ (g act UNIV) f
      ==>
      ?e : 'b -> 'a set.
        BIJ e
          (orbit f g b)
          (IMAGE (left_coset g (stabilizer f g b)) g.carrier) /\
        !a. a IN g.carrier ==>
            e (f a b) = left_coset g (stabilizer f g b) a``;
