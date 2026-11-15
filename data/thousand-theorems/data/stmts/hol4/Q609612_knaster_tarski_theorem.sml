(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q609612, "Knaster–Tarski theorem": the fixed points of a monotone self-map
  of a complete lattice form a complete lattice under the inherited order.
  This file contains no proof.
*)

open HolKernel Parse boolLib;

val q609612_complete_lattice_on_def = new_definition (
  "q609612_complete_lattice_on_def",
  ``q609612_complete_lattice_on
      (carrier : 'a -> bool)
      (leR : 'a -> 'a -> bool)
      (supR : ('a -> bool) -> 'a)
      (infR : ('a -> bool) -> 'a) <=>
      (!x. carrier x ==> leR x x) /\
      (!x y z.
        carrier x /\ carrier y /\ carrier z /\
        leR x y /\ leR y z
        ==>
        leR x z) /\
      (!x y.
        carrier x /\ carrier y /\ leR x y /\ leR y x
        ==>
        x = y) /\
      (!P.
        (!x. P x ==> carrier x)
        ==>
        carrier (supR P) /\
        (!x. P x ==> leR x (supR P)) /\
        (!upper.
          carrier upper /\ (!x. P x ==> leR x upper)
          ==>
          leR (supR P) upper)) /\
      (!P.
        (!x. P x ==> carrier x)
        ==>
        carrier (infR P) /\
        (!x. P x ==> leR (infR P) x) /\
        (!lower.
          carrier lower /\ (!x. P x ==> leR lower x)
          ==>
          leR lower (infR P)))``);

val q609612_monotone_def = new_definition (
  "q609612_monotone_def",
  ``q609612_monotone
      (leR : 'a -> 'a -> bool) (f : 'a -> 'a) <=>
      !x y. leR x y ==> leR (f x) (f y)``);

val fixedPoints_completeLattice =
  ``!(leR : 'a -> 'a -> bool)
      (supR : ('a -> bool) -> 'a)
      (infR : ('a -> bool) -> 'a)
      (f : 'a -> 'a).
      q609612_complete_lattice_on (\x. T) leR supR infR /\
      q609612_monotone leR f
      ==>
      ?fixedSup fixedInf.
        q609612_complete_lattice_on
          (\x. f x = x) leR fixedSup fixedInf``;
