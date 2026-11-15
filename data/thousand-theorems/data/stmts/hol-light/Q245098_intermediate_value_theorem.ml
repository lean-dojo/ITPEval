(*
  Statement-only formalization of Thousand Theorems corpus artifact Q245098,
  (thousand-theorems__hol-light__Q245098), "Intermediate value theorem": a
  continuous function on a closed interval in a dense conditionally complete
  linear order attains every value between its endpoint values. This file
  contains no proof.
*)

let Q245098_INTERMEDIATE_VALUE_THEOREM =
  `let strict =
     \(le:A->A->bool) (x:A) (y:A). le x y /\ ~(x = y) in
   let is_linear_order =
     \(le:A->A->bool).
       (!x:A. le x x) /\
       (!x y:A. le x y /\ le y x ==> x = y) /\
       (!x y z:A. le x y /\ le y z ==> le x z) /\
       (!x y:A. le x y \/ le y x) in
   let bounded_above =
     \(le:A->A->bool) (s:A->bool).
       ?u:A. !x:A. x IN s ==> le x u in
   let bounded_below =
     \(le:A->A->bool) (s:A->bool).
       ?l:A. !x:A. x IN s ==> le l x in
   let is_lub =
     \(le:A->A->bool) (s:A->bool) (u:A).
       (!x:A. x IN s ==> le x u) /\
       (!v:A. (!x:A. x IN s ==> le x v) ==> le u v) in
   let is_glb =
     \(le:A->A->bool) (s:A->bool) (l:A).
       (!x:A. x IN s ==> le l x) /\
       (!v:A. (!x:A. x IN s ==> le v x) ==> le v l) in
   let is_conditionally_complete_linear_order =
     \(le:A->A->bool).
       is_linear_order le /\
       (!s:A->bool.
          ~(s = {}) /\ bounded_above le s
          ==> ?u:A. is_lub le s u) /\
       (!s:A->bool.
          ~(s = {}) /\ bounded_below le s
          ==> ?l:A. is_glb le s l) in
   let is_densely_ordered =
     \(le:A->A->bool).
       !x y:A.
         strict le x y
         ==> ?z:A. strict le x z /\ strict le z y in
   let is_topology =
     \(open_sets:(A->bool)->bool).
       open_sets {} /\
       open_sets (:A) /\
       (!family:(A->bool)->bool.
          (!u:A->bool. u IN family ==> open_sets u)
          ==> open_sets (UNIONS family)) /\
       (!u v:A->bool.
          open_sets u /\ open_sets v
          ==> open_sets (u INTER v)) in
   let is_order_topology =
     \(le:A->A->bool) (open_sets:(A->bool)->bool).
       is_topology open_sets /\
       (!a:A. open_sets {x:A | strict le x a}) /\
       (!a:A. open_sets {x:A | strict le a x}) /\
       (!candidate:(A->bool)->bool.
          is_topology candidate /\
          (!a:A. candidate {x:A | strict le x a}) /\
          (!a:A. candidate {x:A | strict le a x})
          ==> !u:A->bool. open_sets u ==> candidate u) in
   let is_linear_order_d =
     \(le:D->D->bool).
       (!x:D. le x x) /\
       (!x y:D. le x y /\ le y x ==> x = y) /\
       (!x y z:D. le x y /\ le y z ==> le x z) /\
       (!x y:D. le x y \/ le y x) in
   let is_topology_d =
     \(open_sets:(D->bool)->bool).
       open_sets {} /\
       open_sets (:D) /\
       (!family:(D->bool)->bool.
          (!u:D->bool. u IN family ==> open_sets u)
          ==> open_sets (UNIONS family)) /\
       (!u v:D->bool.
          open_sets u /\ open_sets v
          ==> open_sets (u INTER v)) in
   let is_order_closed_topology =
     \(le:D->D->bool) (open_sets:(D->bool)->bool).
       is_topology_d open_sets /\
       (!x y:D.
          ~le x y
          ==> ?u v:D->bool.
                open_sets u /\ open_sets v /\
                x IN u /\ y IN v /\
                (!x' y':D.
                   x' IN u /\ y' IN v ==> ~le x' y')) in
   let continuous_on =
     \(open_a:(A->bool)->bool) (open_d:(D->bool)->bool)
      (f:A->D) (s:A->bool).
       !u:D->bool.
         open_d u
         ==> ?v:A->bool.
               open_a v /\
               (!x:A. x IN s ==> (f x IN u <=> x IN v)) in
   !le_a:A->A->bool.
   !open_a:(A->bool)->bool.
   !le_d:D->D->bool.
   !open_d:(D->bool)->bool.
   !f:A->D.
   !a b:A.
     is_conditionally_complete_linear_order le_a /\
     is_densely_ordered le_a /\
     is_order_topology le_a open_a /\
     is_linear_order_d le_d /\
     is_order_closed_topology le_d open_d /\
     le_a a b /\
     continuous_on open_a open_d f {x:A | le_a a x /\ le_a x b}
     ==> !t:D.
           le_d (f a) t /\ le_d t (f b)
           ==> ?x:A.
                 le_a a x /\ le_a x b /\ f x = t`;;
