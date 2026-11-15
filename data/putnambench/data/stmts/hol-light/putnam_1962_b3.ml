(*
  Statement-only formalization of PutnamBench artifact putnam_1962_b3:
  a convex subset of the real plane meeting every ray in an exterior point is
  bounded under the stated interior-or-closed hypothesis. This file contains
  no proof.
*)

let statement =
  `let convex =
     \S:(real#real)->bool.
       !x y:real#real. !u v:real.
         x IN S /\ y IN S /\
         &0 <= u /\ &0 <= v /\ u + v = &1
         ==> (u * FST x + v * FST y,
              u * SND x + v * SND y) IN S in
   let origin_interior =
     \S:(real#real)->bool.
       ?e:real.
         &0 < e /\
         !x:real#real.
           (FST x) pow 2 + (SND x) pow 2 < e pow 2
           ==> x IN S in
   let closed =
     \S:(real#real)->bool.
       !x:real#real.
         ~(x IN S)
         ==> ?e:real.
               &0 < e /\
               !y:real#real.
                 (FST y - FST x) pow 2 +
                 (SND y - SND x) pow 2 < e pow 2
                 ==> ~(y IN S) in
   let bounded =
     \S:(real#real)->bool.
       ?b:real.
         !x:real#real.
           x IN S ==> (FST x) pow 2 + (SND x) pow 2 <= b in
   !S:(real#real)->bool.
     convex S /\
     (&0,&0) IN S /\
     (origin_interior S \/ closed S) /\
     (!P:real#real.
        ~(P = (&0,&0))
        ==> ?Q:real#real. ?k:real.
              &0 < k /\
              FST Q = k * FST P /\
              SND Q = k * SND P /\
              ~(Q IN S))
     ==> bounded S`;;
