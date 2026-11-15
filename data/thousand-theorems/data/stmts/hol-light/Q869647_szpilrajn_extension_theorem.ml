(*
  Statement-only formalization of Thousand Theorems corpus artifact Q869647
  (thousand-theorems__hol-light__Q869647), "Szpilrajn extension theorem":
  every partial order on an arbitrary type extends to a linear order on the
  same type. This file contains no proof.
*)

let Q869647_SZPILRAJN_EXTENSION_THEOREM =
  `let is_partial_order =
     \(rel:A->A->bool).
       (!x:A. rel x x) /\
       (!x y z:A. rel x y /\ rel y z ==> rel x z) /\
       (!x y:A. rel x y /\ rel y x ==> x = y) in
   let is_linear_order =
     \(rel:A->A->bool).
       is_partial_order rel /\
       (!x y:A. rel x y \/ rel y x) in
   !r:A->A->bool.
     is_partial_order r
     ==> ?s:A->A->bool.
           is_linear_order s /\
           (!x y:A. r x y ==> s x y)`;;
