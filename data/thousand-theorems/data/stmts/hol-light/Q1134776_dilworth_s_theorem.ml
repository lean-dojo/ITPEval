(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1134776,
  "Dilworth's theorem": for every finite carrier equipped with a partial
  order, the minimum cardinality of a chain partition equals the maximum
  cardinality of an antichain. This file contains no proof.
*)

let Q1134776_DILWORTH_THEOREM =
  `let is_partial_order_on =
     \(carrier:A->bool) (le:A->A->bool).
       (!x:A. x IN carrier ==> le x x) /\
       (!x y z:A.
          x IN carrier /\ y IN carrier /\ z IN carrier /\
          le x y /\ le y z
          ==> le x z) /\
       (!x y:A.
          x IN carrier /\ y IN carrier /\ le x y /\ le y x
          ==> x = y) in
   let is_chain =
     \(carrier:A->bool) (le:A->A->bool) (s:A->bool).
       s SUBSET carrier /\
       !x y:A. x IN s /\ y IN s ==> le x y \/ le y x in
   let is_antichain =
     \(carrier:A->bool) (le:A->A->bool) (s:A->bool).
       s SUBSET carrier /\
       !x y:A.
         x IN s /\ y IN s /\ ~(x = y)
         ==> ~(le x y) /\ ~(le y x) in
   let is_chain_partition =
     \(carrier:A->bool) (le:A->A->bool) (C:(A->bool)->bool).
       (!x:A.
          x IN carrier ==> ?!c:A->bool. c IN C /\ x IN c) /\
       (!c:A->bool. c IN C ==> is_chain carrier le c) in
   let min_chain_partition =
     \(carrier:A->bool) (le:A->A->bool).
       minimal n.
         ?C:(A->bool)->bool.
           is_chain_partition carrier le C /\ CARD C = n in
   let antichain_width =
     \(carrier:A->bool) (le:A->A->bool).
       minimal n.
         !s:A->bool.
           is_antichain carrier le s ==> CARD s <= n in
   !carrier:A->bool.
     !le:A->A->bool.
       FINITE carrier /\
       is_partial_order_on carrier le
       ==> min_chain_partition carrier le =
           antichain_width carrier le`;;
