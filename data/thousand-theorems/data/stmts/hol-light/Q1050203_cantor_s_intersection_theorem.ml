(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1050203,
  "Cantor's intersection theorem": every nonempty downward-directed family of
  nonempty compact closed subsets of an arbitrary topological space has
  nonempty total intersection. This file contains no proof.
*)

let Q1050203_CANTOR_INTERSECTION_THEOREM =
  `let is_topology =
     \(open_sets:(A->bool)->bool).
       open_sets {} /\
       open_sets (UNIV:A->bool) /\
       (!C:(A->bool)->bool.
          (!U:A->bool. U IN C ==> open_sets U)
          ==> open_sets (UNIONS C)) /\
       (!U V:A->bool.
          open_sets U /\ open_sets V ==> open_sets (U INTER V)) in
   let is_closed =
     \(open_sets:(A->bool)->bool) (U:A->bool).
       open_sets ((UNIV:A->bool) DIFF U) in
   let is_compact =
     \(open_sets:(A->bool)->bool) (K:A->bool).
       !C:(A->bool)->bool.
         (!U:A->bool. U IN C ==> open_sets U) /\
         K SUBSET UNIONS C
         ==> ?D:(A->bool)->bool.
               D SUBSET C /\
               FINITE D /\
               K SUBSET UNIONS D in
   !open_sets:(A->bool)->bool.
   !S:(A->bool)->bool.
     is_topology open_sets /\
     (?U:A->bool. U IN S) /\
     (!U V:A->bool.
        U IN S /\ V IN S
        ==> ?W:A->bool. W IN S /\ W SUBSET U /\ W SUBSET V) /\
     (!U:A->bool.
        U IN S
        ==> ~(U = {}) /\
            is_compact open_sets U /\
            is_closed open_sets U)
     ==> ?x:A. x IN INTERS S`;;
