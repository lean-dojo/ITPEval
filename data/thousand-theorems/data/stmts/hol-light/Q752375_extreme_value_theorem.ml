(*
  Statement-only formalization of Thousand Theorems corpus artifact Q752375,
  "Extreme value theorem": a continuous function on a nonempty compact set,
  valued in a linear order whose lower intervals are closed, attains its
  minimum on that set. This file contains no proof.
*)

let Q752375_EXTREME_VALUE_THEOREM =
  `let is_topology =
     \(open_sets:(A->bool)->bool).
       open_sets {} /\
       open_sets (UNIV:A->bool) /\
       (!C:(A->bool)->bool.
          (!U:A->bool. U IN C ==> open_sets U)
          ==> open_sets (UNIONS C)) /\
       (!U V:A->bool.
          open_sets U /\ open_sets V
          ==> open_sets (U INTER V)) in
   let is_topology_b =
     \(open_sets:(B->bool)->bool).
       open_sets {} /\
       open_sets (UNIV:B->bool) /\
       (!C:(B->bool)->bool.
          (!U:B->bool. U IN C ==> open_sets U)
          ==> open_sets (UNIONS C)) /\
       (!U V:B->bool.
          open_sets U /\ open_sets V
          ==> open_sets (U INTER V)) in
   let is_closed =
     \(open_sets:(A->bool)->bool) (U:A->bool).
       open_sets ((UNIV:A->bool) DIFF U) in
   let is_compact =
     \(open_sets:(B->bool)->bool) (K:B->bool).
       !C:(B->bool)->bool.
         (!U:B->bool. U IN C ==> open_sets U) /\
         K SUBSET UNIONS C
         ==> ?D:(B->bool)->bool.
               D SUBSET C /\
               FINITE D /\
               K SUBSET UNIONS D in
   let is_linear_order =
     \(le:A->A->bool).
       (!x:A. le x x) /\
       (!x y:A. le x y /\ le y x ==> x = y) /\
       (!x y z:A. le x y /\ le y z ==> le x z) /\
       (!x y:A. le x y \/ le y x) in
   let is_continuous_on =
     \(open_a:(A->bool)->bool) (open_b:(B->bool)->bool)
      (f:B->A) (s:B->bool).
       !V:A->bool.
         open_a V
         ==> ?U:B->bool.
               open_b U /\
               {x:B | x IN s /\ f x IN V} = s INTER U in
   !open_a:(A->bool)->bool.
   !open_b:(B->bool)->bool.
   !le:A->A->bool.
   !s:B->bool.
   !f:B->A.
     is_topology open_a /\
     is_topology_b open_b /\
     is_linear_order le /\
     (!a:A. is_closed open_a {x:A | le x a}) /\
     is_compact open_b s /\
     (?x:B. x IN s) /\
     is_continuous_on open_a open_b f s
     ==> ?x:B.
           x IN s /\
           !y:B. y IN s ==> le (f x) (f y)`;;
