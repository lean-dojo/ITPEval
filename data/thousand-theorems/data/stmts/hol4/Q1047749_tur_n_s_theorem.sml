(*
  Statement-only formalization of the Thousand Theorems artifact Q1047749,
  "Turán's theorem": a finite simple graph is maximal among graphs with no
  (r + 1)-clique exactly when it is isomorphic to the balanced complete
  r-partite Turán graph. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory;

val q1047749_simple_graph_def = new_definition (
  "q1047749_simple_graph_def",
  ``q1047749_simple_graph
      (vertices : 'a set) (adj : 'a -> 'a -> bool) <=>
      (!(u : 'a) (v : 'a).
         adj u v ==> u IN vertices /\ v IN vertices) /\
      (!(v : 'a). ~adj v v) /\
      (!(u : 'a) (v : 'a). adj u v <=> adj v u)``);

val q1047749_edge_arcs_def = new_definition (
  "q1047749_edge_arcs_def",
  ``q1047749_edge_arcs
      (vertices : 'a set) (adj : 'a -> 'a -> bool) =
      {p : 'a # 'a |
         FST p IN vertices /\
         SND p IN vertices /\
         adj (FST p) (SND p)}``);

val q1047749_clique_free_def = new_definition (
  "q1047749_clique_free_def",
  ``q1047749_clique_free
      (vertices : 'a set) (adj : 'a -> 'a -> bool) (k : num) <=>
      ~(?C : 'a set.
          FINITE C /\
          C SUBSET vertices /\
          CARD C = k /\
          !(u : 'a) (v : 'a).
            u IN C /\ v IN C /\ u <> v
            ==>
            adj u v)``);

val q1047749_is_turan_maximal_def = new_definition (
  "q1047749_is_turan_maximal_def",
  ``q1047749_is_turan_maximal
      (vertices : 'a set) (adj : 'a -> 'a -> bool) (r : num) <=>
      q1047749_clique_free vertices adj (r + 1) /\
      !other : 'a -> 'a -> bool.
        q1047749_simple_graph vertices other /\
        q1047749_clique_free vertices other (r + 1)
        ==>
        CARD (q1047749_edge_arcs vertices other) <=
        CARD (q1047749_edge_arcs vertices adj)``);

val isTuranMaximal_iff_nonempty_iso_turanGraph =
  ``!vertices : 'a set. !adj : 'a -> 'a -> bool. !r : num.
      FINITE vertices /\
      q1047749_simple_graph vertices adj /\
      0 < r
      ==>
      (q1047749_is_turan_maximal vertices adj r
       <=>
       ?f : 'a -> num.
         BIJ f vertices {i : num | i < CARD vertices} /\
         !(u : 'a) (v : 'a).
           u IN vertices /\ v IN vertices
           ==>
           (adj u v <=> f u MOD r <> f v MOD r))``;
