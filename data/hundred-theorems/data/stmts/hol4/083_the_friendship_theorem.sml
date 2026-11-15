(*
  Statement-only formalization of Hundred Theorems artifact
  hundred-theorems__hol4__083, cataloged as "The Friendship Theorem": every
  finite irreflexive symmetric friendship relation in which each pair of
  distinct vertices has exactly one common friend has a vertex adjacent to
  every other vertex. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory;

val friendship_theorem =
  ``!friend : 'a -> 'a -> bool.
      FINITE (UNIV : 'a set) /\
      (!x. ~friend x x) /\
      (!x y. friend x y ==> friend y x) /\
      (!x y. x <> y ==> ?!z. friend x z /\ friend y z)
      ==>
      ?u. !v. v <> u ==> friend u v``;
