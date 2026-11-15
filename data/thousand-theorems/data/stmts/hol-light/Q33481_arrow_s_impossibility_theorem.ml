(*
  Statement-only formalization of Thousand Theorems corpus artifact Q33481,
  "Arrow's impossibility theorem": every social welfare function on a finite
  electorate and at least three alternatives that satisfies weak Pareto and
  independence of irrelevant alternatives is dictatorial. This file contains
  no proof.
*)

let Q33481_ARROWS_IMPOSSIBILITY_THEOREM =
  `let is_preference_order =
     \(r:A->A->bool).
       (!x:A. r x x) /\
       (!x y:A. r x y \/ r y x) /\
       (!x y z:A. r x y /\ r y z ==> r x z) in
   let strictly_prefers =
     \(r:A->A->bool) (x:A) (y:A).
       r x y /\ ~(r y x) in
   let is_profile =
     \(voters:V->bool) (R:V->A->A->bool).
       !i:V. i IN voters ==> is_preference_order (R i) in
   let same_pair_order =
     \(r:A->A->bool) (r':A->A->bool) (x:A) (y:A).
       (strictly_prefers r x y <=> strictly_prefers r' x y) /\
       (strictly_prefers r y x <=> strictly_prefers r' y x) in
   let is_social_welfare_function =
     \(voters:V->bool)
      (f:(V->A->A->bool)->A->A->bool).
       (!R:V->A->A->bool.
          is_profile voters R
          ==> is_preference_order (f R)) /\
       (!R R':V->A->A->bool.
          is_profile voters R /\
          is_profile voters R' /\
          (!i:V.
             i IN voters
             ==> !x y:A. R i x y <=> R' i x y)
          ==> !x y:A. f R x y <=> f R' x y) in
   let weak_pareto =
     \(voters:V->bool) (alternatives:A->bool)
      (f:(V->A->A->bool)->A->A->bool).
       !x y:A. !R:V->A->A->bool.
         x IN alternatives /\
         y IN alternatives /\
         is_profile voters R /\
         (!i:V. i IN voters ==> strictly_prefers (R i) x y)
         ==> strictly_prefers (f R) x y in
   let independent_of_irrelevant_alternatives =
     \(voters:V->bool) (alternatives:A->bool)
      (f:(V->A->A->bool)->A->A->bool).
       !R R':V->A->A->bool. !x y:A.
         is_profile voters R /\
         is_profile voters R' /\
         x IN alternatives /\
         y IN alternatives /\
         (!i:V.
            i IN voters
            ==> same_pair_order (R i) (R' i) x y)
         ==> same_pair_order (f R) (f R') x y in
   let is_dictatorship =
     \(voters:V->bool) (alternatives:A->bool)
      (f:(V->A->A->bool)->A->A->bool).
       ?i:V.
         i IN voters /\
         !x y:A. !R:V->A->A->bool.
           x IN alternatives /\
           y IN alternatives /\
           is_profile voters R /\
           strictly_prefers (R i) x y
           ==> strictly_prefers (f R) x y in
   !voters:V->bool.
   !alternatives:A->bool.
   !f:(V->A->A->bool)->A->A->bool.
     FINITE voters /\
     FINITE alternatives /\
     3 <= CARD alternatives /\
     is_social_welfare_function voters f /\
     weak_pareto voters alternatives f /\
     independent_of_irrelevant_alternatives voters alternatives f
     ==> is_dictatorship voters alternatives f`;;
