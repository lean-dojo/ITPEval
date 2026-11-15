(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1052678,
  "Baire category theorem": in an arbitrary Baire topological space, every
  countable intersection of open dense sets is dense. This file contains no
  proof.
*)

let Q1052678_BAIRE_CATEGORY_THEOREM =
  `let is_topology =
     \(X:A->bool) (open_sets:(A->bool)->bool).
       open_sets {} /\
       open_sets X /\
       (!U:A->bool. open_sets U ==> U SUBSET X) /\
       (!C:(A->bool)->bool.
          (!U:A->bool. U IN C ==> open_sets U)
          ==> open_sets (UNIONS C)) /\
       (!U V:A->bool.
          open_sets U /\ open_sets V
          ==> open_sets (U INTER V)) in
   let dense =
     \(X:A->bool) (open_sets:(A->bool)->bool) (D:A->bool).
       D SUBSET X /\
       !U:A->bool.
         open_sets U /\ ~(U = {})
         ==> ~(U INTER D = {}) in
   let is_baire_space =
     \(X:A->bool) (open_sets:(A->bool)->bool).
       !f:num->A->bool.
         (!n. open_sets (f n)) /\
         (!n. dense X open_sets (f n))
         ==> dense X open_sets
               (X INTER INTERS (IMAGE f (:num))) in
   !X:A->bool.
   !open_sets:(A->bool)->bool.
   !S:(A->bool)->bool.
     is_topology X open_sets /\
     is_baire_space X open_sets /\
     (!U:A->bool. U IN S ==> open_sets U) /\
     COUNTABLE S /\
     (!U:A->bool. U IN S ==> dense X open_sets U)
     ==> dense X open_sets (X INTER INTERS S)`;;
