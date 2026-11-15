(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q510197 (thousand-theorems__hol4__Q510197), "Tutte theorem": a finite,
  possibly empty, simple graph has a perfect matching if and only if deleting
  any vertex set leaves at most that many odd connected components. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory relationTheory;

val q510197_simple_graph_def = new_definition (
  "q510197_simple_graph_def",
  ``q510197_simple_graph
      (vertices : 'a set) (adj : 'a -> 'a -> bool) <=>
      (!(u : 'a) (v : 'a).
         adj u v ==> u IN vertices /\ v IN vertices) /\
      (!(v : 'a).
         v IN vertices ==> ~adj v v) /\
      (!(u : 'a) (v : 'a).
         u IN vertices /\ v IN vertices
         ==>
         (adj u v <=> adj v u))``);

val q510197_deleted_adj_def = new_definition (
  "q510197_deleted_adj_def",
  ``q510197_deleted_adj
      (vertices : 'a set) (adj : 'a -> 'a -> bool)
      (removed : 'a set) (u : 'a) (v : 'a) <=>
      u IN vertices /\
      v IN vertices /\
      u NOTIN removed /\
      v NOTIN removed /\
      adj u v``);

val q510197_component_def = new_definition (
  "q510197_component_def",
  ``q510197_component
      (vertices : 'a set) (adj : 'a -> 'a -> bool)
      (removed : 'a set) (root : 'a) =
      {v : 'a |
        root IN vertices /\
        root NOTIN removed /\
        v IN vertices /\
        v NOTIN removed /\
        RTC (q510197_deleted_adj vertices adj removed) root v}``);

val q510197_odd_components_def = new_definition (
  "q510197_odd_components_def",
  ``q510197_odd_components
      (vertices : 'a set) (adj : 'a -> 'a -> bool)
      (removed : 'a set) =
      {component : 'a set |
        ?root : 'a.
          root IN vertices /\
          root NOTIN removed /\
          component = q510197_component vertices adj removed root /\
          ODD (CARD component)}``);

val q510197_is_perfect_matching_def = new_definition (
  "q510197_is_perfect_matching_def",
  ``q510197_is_perfect_matching
      (vertices : 'a set) (adj : 'a -> 'a -> bool)
      (matching : 'a -> 'a -> bool) <=>
      (!(u : 'a) (v : 'a).
         matching u v
         ==>
         u IN vertices /\ v IN vertices /\ adj u v) /\
      (!(u : 'a) (v : 'a).
         u IN vertices /\ v IN vertices
         ==>
         (matching u v <=> matching v u)) /\
      (!(u : 'a).
         u IN vertices
         ==>
         ?!v : 'a. v IN vertices /\ matching u v)``);

val q510197_is_tutte_violator_def = new_definition (
  "q510197_is_tutte_violator_def",
  ``q510197_is_tutte_violator
      (vertices : 'a set) (adj : 'a -> 'a -> bool)
      (removed : 'a set) <=>
      removed SUBSET vertices /\
      CARD removed <
        CARD (q510197_odd_components vertices adj removed)``);

val tutte =
  ``!vertices : 'a set. !adj : 'a -> 'a -> bool.
      FINITE vertices /\
      q510197_simple_graph vertices adj
      ==>
      ((?matching : 'a -> 'a -> bool.
          q510197_is_perfect_matching vertices adj matching)
       <=>
       !removed : 'a set.
         removed SUBSET vertices
         ==>
         ~q510197_is_tutte_violator vertices adj removed)``;
