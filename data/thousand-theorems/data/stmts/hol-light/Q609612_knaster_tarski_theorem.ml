(*
  Statement-only formalization of Thousand Theorems corpus artifact Q609612
  (thousand-theorems__hol-light__Q609612), "Knaster–Tarski theorem": the fixed
  points of a monotone self-map of a complete lattice form a complete lattice
  under the inherited order. This file contains no proof.
*)

let Q609612_KNASTER_TARSKI_THEOREM =
  `let is_partial_order =
     \(le:A->A->bool).
       (!x:A. le x x) /\
       (!x y:A. le x y /\ le y x ==> x = y) /\
       (!x y z:A. le x y /\ le y z ==> le x z) in
   let is_supremum =
     \(le:A->A->bool) (s:A->bool) (u:A).
       (!x:A. x IN s ==> le x u) /\
       (!v:A. (!x:A. x IN s ==> le x v) ==> le u v) in
   let is_infimum =
     \(le:A->A->bool) (s:A->bool) (l:A).
       (!x:A. x IN s ==> le l x) /\
       (!v:A. (!x:A. x IN s ==> le v x) ==> le v l) in
   let is_complete_lattice =
     \(le:A->A->bool) (sSup:(A->bool)->A) (sInf:(A->bool)->A).
       is_partial_order le /\
       (!s:A->bool. is_supremum le s (sSup s)) /\
       (!s:A->bool. is_infimum le s (sInf s)) in
   let is_monotone =
     \(le:A->A->bool) (f:A->A).
       !x y:A. le x y ==> le (f x) (f y) in
   let is_partial_order_on =
     \(carrier:A->bool) (le:A->A->bool).
       (!x:A. carrier x ==> le x x) /\
       (!x y:A.
          carrier x /\ carrier y /\ le x y /\ le y x
          ==> x = y) /\
       (!x y z:A.
          carrier x /\ carrier y /\ carrier z /\
          le x y /\ le y z
          ==> le x z) in
   let is_supremum_in =
     \(carrier:A->bool) (le:A->A->bool) (s:A->bool) (u:A).
       carrier u /\
       (!x:A. x IN s ==> carrier x /\ le x u) /\
       (!v:A.
          carrier v /\ (!x:A. x IN s ==> le x v)
          ==> le u v) in
   let is_infimum_in =
     \(carrier:A->bool) (le:A->A->bool) (s:A->bool) (l:A).
       carrier l /\
       (!x:A. x IN s ==> carrier x /\ le l x) /\
       (!v:A.
          carrier v /\ (!x:A. x IN s ==> le v x)
          ==> le v l) in
   let is_complete_lattice_on =
     \(carrier:A->bool) (le:A->A->bool).
       is_partial_order_on carrier le /\
       (!s:A->bool.
          (!x:A. x IN s ==> carrier x)
          ==> ?u:A. is_supremum_in carrier le s u) /\
       (!s:A->bool.
          (!x:A. x IN s ==> carrier x)
          ==> ?l:A. is_infimum_in carrier le s l) in
   !le:A->A->bool.
   !sSup:(A->bool)->A.
   !sInf:(A->bool)->A.
   !f:A->A.
     is_complete_lattice le sSup sInf /\
     is_monotone le f
     ==> is_complete_lattice_on (\x:A. f x = x) le`;;
