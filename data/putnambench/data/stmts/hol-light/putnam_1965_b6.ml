(*
  Statement-only formalization of PutnamBench artifact putnam_1965_b6:
  four distinct points in the real plane such that every circle through the
  first pair intersects every circle through the second pair are collinear
  or cocyclic. This file contains no proof.
*)

let statement =
  `let edist =
     \(x:real#real) (y:real#real).
       sqrt ((FST x - FST y) pow 2 + (SND x - SND y) pow 2) in
   let collinear3 =
     \(a:real#real) (b:real#real) (c:real#real).
       (FST b - FST a) * (SND c - SND a) =
       (SND b - SND a) * (FST c - FST a) in
   !A B C D:real#real.
     ~(A = B) /\ ~(A = C) /\ ~(A = D) /\
     ~(B = C) /\ ~(B = D) /\ ~(C = D) /\
     (!r s:real. !P Q:real#real.
        &0 < r /\ &0 < s /\
        edist P A = r /\ edist P B = r /\
        edist Q C = s /\ edist Q D = s
        ==> ?X:real#real. edist P X = r /\ edist Q X = s)
     ==>
     (collinear3 A B C /\ collinear3 A B D \/
      ?r:real. ?P:real#real.
        &0 < r /\
        edist P A = r /\ edist P B = r /\
        edist P C = r /\ edist P D = r)`;;
