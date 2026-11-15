(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1065257,
  "Squeeze theorem": for functions into an arbitrary preorder with its order
  topology, convergence of lower and upper bounds to the same point together
  with eventual pointwise bounds implies convergence of the middle function.
  This file contains no proof.
*)

let Q1065257_SQUEEZE_THEOREM =
  `let is_preorder =
     \(le:A->A->bool).
       (!x:A. le x x) /\
       (!x y z:A. le x y /\ le y z ==> le x z) in
   let is_topology =
     \(open_sets:(A->bool)->bool).
       open_sets {} /\
       open_sets (UNIV:A->bool) /\
       (!C:(A->bool)->bool.
          (!U:A->bool. U IN C ==> open_sets U)
          ==> open_sets (UNIONS C)) /\
       (!U V:A->bool.
          open_sets U /\ open_sets V
          ==> open_sets (U INTER V)) in
   let is_order_topology =
     \(le:A->A->bool) (open_sets:(A->bool)->bool).
       !U:A->bool.
         open_sets U <=>
         !candidate:(A->bool)->bool.
           is_topology candidate /\
           (!a:A. candidate {x:A | le a x /\ ~(le x a)}) /\
           (!a:A. candidate {x:A | le x a /\ ~(le a x)})
           ==> candidate U in
   let is_filter =
     \(sets:(B->bool)->bool).
       sets (UNIV:B->bool) /\
       (!S U:B->bool.
          sets S /\ S SUBSET U ==> sets U) /\
       (!S U:B->bool.
          sets S /\ sets U ==> sets (S INTER U)) in
   let tends_to =
     \(open_sets:(A->bool)->bool)
      (sets:(B->bool)->bool) (u:B->A) (a:A).
       !U:A->bool.
         open_sets U /\ a IN U
         ==> sets {x:B | u x IN U} in
   !le:A->A->bool.
   !open_sets:(A->bool)->bool.
   !sets:(B->bool)->bool.
   !f g h:B->A.
   !a:A.
     is_preorder le /\
     is_topology open_sets /\
     is_order_topology le open_sets /\
     is_filter sets /\
     tends_to open_sets sets g a /\
     tends_to open_sets sets h a /\
     sets {x:B | le (g x) (f x)} /\
     sets {x:B | le (f x) (h x)}
     ==> tends_to open_sets sets f a`;;
