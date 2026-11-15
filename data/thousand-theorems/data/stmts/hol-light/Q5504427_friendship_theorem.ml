(*
  Statement-only formalization of Thousand Theorems corpus artifact Q5504427,
  "Friendship theorem": every finite simple undirected graph in which each pair
  of distinct vertices has exactly one common neighbor contains a vertex
  adjacent to every other distinct vertex. This file contains no proof.
*)

let Q5504427_FRIENDSHIP_THEOREM =
  `!G:A->A->bool.
     FINITE (UNIV:A->bool) /\
     (!v:A. ~(G v v)) /\
     (!v w:A. G v w <=> G w v) /\
     (!v w:A.
        ~(v = w)
        ==> CARD {x:A | G v x /\ G w x} = 1)
     ==> ?v:A. !w:A. ~(v = w) ==> G v w`;;
