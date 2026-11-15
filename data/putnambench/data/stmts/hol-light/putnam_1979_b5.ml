(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1979_b5:
  a closed convex planar set containing the origin, no other integer lattice
  point, and equal Lebesgue area in all four quadrants has total area at most
  four. This file contains no proof.
*)

let statement =
  `let closed =
     \S:(real#real)->bool.
       !x:real#real.
         ~(x IN S)
         ==> ?e:real.
               &0 < e /\
               !y:real#real.
                 (FST y - FST x) pow 2 +
                 (SND y - SND x) pow 2 < e pow 2
                 ==> ~(y IN S) in
   let convex =
     \S:(real#real)->bool.
       !x y:real#real. !u v:real.
         x IN S /\ y IN S /\
         &0 <= u /\ &0 <= v /\ u + v = &1
         ==> (u * FST x + v * FST y,
              u * SND x + v * SND y) IN S in
   let cover_bound =
     \(S:(real#real)->bool) (B:real).
       &0 <= B /\
       ?a b c d:num->real.
         (!k. a k <= b k /\ c k <= d k) /\
         (!x. x IN S
              ==> ?k.
                    a k < FST x /\ FST x < b k /\
                    c k < SND x /\ SND x < d k) /\
         (!N.
            sum (0..N)
              (\k. (b k - a k) * (d k - c k)) <= B) in
   let outer_area_le =
     \(S:(real#real)->bool) (r:real).
       !e:real.
         &0 < e
         ==> ?B:real. cover_bound S B /\ B <= r + e in
   let equal_outer_area =
     \(s:(real#real)->bool) (t:(real#real)->bool).
       !r:real. outer_area_le s r <=> outer_area_le t r in
   let quadrant_pp =
     {x:real#real | &0 <= FST x /\ &0 <= SND x} in
   let quadrant_pn =
     {x:real#real | &0 <= FST x /\ SND x <= &0} in
   let quadrant_np =
     {x:real#real | FST x <= &0 /\ &0 <= SND x} in
   let quadrant_nn =
     {x:real#real | FST x <= &0 /\ SND x <= &0} in
   !C:(real#real)->bool.
     closed C /\
     convex C /\
     (&0,&0) IN C /\
     (!a b:int.
        (~(a = &0) \/ ~(b = &0))
        ==> ~((real_of_int a,real_of_int b) IN C)) /\
     equal_outer_area (C INTER quadrant_pp) (C INTER quadrant_pn) /\
     equal_outer_area (C INTER quadrant_pn) (C INTER quadrant_np) /\
     equal_outer_area (C INTER quadrant_np) (C INTER quadrant_nn)
     ==> outer_area_le C (&4)`;;
