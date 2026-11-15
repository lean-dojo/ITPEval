(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2018_a6:
  rationality of the ratio of two triangle areas when all six squared
  pairwise distances among four noncollinear plane points are rational.
  This file contains no proof.
*)

let statement =
  `let squared_distance =
     \(P:real#real) (Q:real#real).
       (FST P - FST Q) pow 2 + (SND P - SND Q) pow 2 in
   let det2 =
     \(P:real#real) (Q:real#real) (R:real#real).
       (FST Q - FST P) * (SND R - SND P) -
       (SND Q - SND P) * (FST R - FST P) in
   let triangle_area =
     \(P:real#real) (Q:real#real) (R:real#real).
       abs (det2 P Q R) / &2 in
   let rational_real =
     \x:real. ?p q:num. ~(q = 0) /\ abs x = &p / &q in
   !A B C D:real#real.
     ~(det2 A B C = &0) /\
     ~(det2 A B D = &0) /\
     ~(det2 A C D = &0) /\
     ~(det2 B C D = &0) /\
     rational_real (squared_distance A B) /\
     rational_real (squared_distance A C) /\
     rational_real (squared_distance A D) /\
     rational_real (squared_distance B C) /\
     rational_real (squared_distance B D) /\
     rational_real (squared_distance C D)
     ==>
     rational_real
       (triangle_area A B C / triangle_area A B D)`;;
