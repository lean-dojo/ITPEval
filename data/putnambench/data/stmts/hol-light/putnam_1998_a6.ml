(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1998_a6:
  three distinct lattice points in the real plane satisfying a two-side
  distance-area inequality form three vertices of a square. This file contains
  no proof.
*)

let statement =
  `let squared_distance =
     \(P:real^2) (Q:real^2).
       (P$1 - Q$1) pow 2 + (P$2 - Q$2) pow 2 in
   let distance =
     \(P:real^2) (Q:real^2). sqrt (squared_distance P Q) in
   let inner_product =
     \(P:real^2) (Q:real^2).
       P$1 * Q$1 + P$2 * Q$2 in
   let triangle_area =
     \(P:real^2) (Q:real^2) (R:real^2).
       abs ((Q$1 - P$1) * (R$2 - P$2) -
            (Q$2 - P$2) * (R$1 - P$1)) / &2 in
   !A B C:real^2.
   !threesquare:real^2->real^2->real^2->bool.
     (!i:num.
        1 <= i /\ i <= 2
        ==> ?a b c:int.
              A$i = real_of_int a /\
              B$i = real_of_int b /\
              C$i = real_of_int c) /\
     ~(A = B) /\ ~(A = C) /\ ~(B = C) /\
     (distance A B + distance B C) pow 2 <
       &8 * triangle_area A B C + &1 /\
     threesquare =
       (\P Q R.
          distance Q P = distance Q R /\
          inner_product
            (lambda i. P$i - Q$i)
            (lambda i. R$i - Q$i) = &0)
     ==>
     threesquare A B C \/
     threesquare B C A \/
     threesquare C A B`;;
