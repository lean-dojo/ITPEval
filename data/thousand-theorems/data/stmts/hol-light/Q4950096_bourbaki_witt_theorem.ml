(*
  Statement-only formalization of Thousand Theorems corpus artifact Q4950096,
  "Bourbaki-Witt theorem": every inflationary self-map of a nonempty
  chain-complete partial order has a fixed point. This file contains no proof.
*)

let Q4950096_BOURBAKI_WITT_THEOREM =
  `let is_partial_order =
     \(le:A->A->bool).
       (!x:A. le x x) /\
       (!x y:A. le x y /\ le y x ==> x = y) /\
       (!x y z:A. le x y /\ le y z ==> le x z) in
   let is_chain =
     \(le:A->A->bool) (s:A->bool).
       !x y:A. s x /\ s y ==> le x y \/ le y x in
   let is_supremum =
     \(le:A->A->bool) (s:A->bool) (u:A).
       (!x:A. s x ==> le x u) /\
       (!v:A. (!x:A. s x ==> le x v) ==> le u v) in
   let is_chain_complete_partial_order =
     \(le:A->A->bool) (cSup:(A->bool)->A).
       is_partial_order le /\
       (!s:A->bool.
          (?x:A. s x) /\ is_chain le s
          ==> is_supremum le s (cSup s)) in
   !le:A->A->bool.
   !cSup:(A->bool)->A.
   !f:A->A.
     is_chain_complete_partial_order le cSup /\
     (!x:A. le x (f x))
     ==> ?x:A. f x = x`;;
