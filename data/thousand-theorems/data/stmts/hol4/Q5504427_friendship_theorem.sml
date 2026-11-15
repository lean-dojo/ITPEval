(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q5504427 (thousand-theorems__hol4__Q5504427), "Friendship theorem": every
  finite nonempty simple graph in which each pair of distinct vertices has
  exactly one common neighbor contains a vertex adjacent to every other
  vertex. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory;

val friendship_theorem =
  ``!adj : 'a -> 'a -> bool.
      FINITE (UNIV : 'a set) /\
      (!(v : 'a). ~adj v v) /\
      (!(v : 'a) (w : 'a). adj v w <=> adj w v) /\
      (!(v : 'a) (w : 'a).
         v <> w ==> CARD {u : 'a | adj v u /\ adj w u} = 1)
      ==>
      ?v : 'a. !(w : 'a). v <> w ==> adj v w``;
