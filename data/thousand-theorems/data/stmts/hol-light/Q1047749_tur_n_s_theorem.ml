(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1047749,
  "Turán's theorem": for positive r, a finite simple graph is maximal among
  graphs with no (r + 1)-clique exactly when it is isomorphic to the balanced
  complete r-partite Turán graph. This file contains no proof.
*)

let Q1047749_TURAN_THEOREM =
  `let simple_graph_on =
     \(V:A->bool) (G:A->A->bool).
       (!x. x IN V ==> ~(G x x)) /\
       (!x y. x IN V /\ y IN V ==> (G x y <=> G y x)) in
   let clique_free_on =
     \(V:A->bool) (G:A->A->bool) (k:num).
       ~(?c:A->bool.
           FINITE c /\
           c SUBSET V /\
           CARD c = k /\
           (!x y. x IN c /\ y IN c /\ ~(x = y) ==> G x y)) in
   let directed_edges =
     \(V:A->bool) (G:A->A->bool).
       {(x,y) | x IN V /\ y IN V /\ G x y} in
   let is_turan_maximal =
     \(V:A->bool) (G:A->A->bool) (r:num).
       clique_free_on V G (r + 1) /\
       (!H:A->A->bool.
          simple_graph_on V H /\ clique_free_on V H (r + 1)
          ==> CARD (directed_edges V H) <= CARD (directed_edges V G)) in
   let isomorphic_to_turan =
     \(V:A->bool) (G:A->A->bool) (r:num).
       ?f:A->num.
         (!x. x IN V ==> f x < CARD V) /\
         (!x y. x IN V /\ y IN V /\ f x = f y ==> x = y) /\
         (!i. i < CARD V ==> ?x. x IN V /\ f x = i) /\
         (!x y.
            x IN V /\ y IN V
            ==> (G x y <=> ~(f x MOD r = f y MOD r))) in
   !V:A->bool. !G:A->A->bool. !r:num.
     FINITE V /\ simple_graph_on V G /\ 0 < r
     ==> (is_turan_maximal V G r <=> isomorphic_to_turan V G r)`;;
