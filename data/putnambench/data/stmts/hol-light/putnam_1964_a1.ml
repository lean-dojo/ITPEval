(*
  Statement-only formalization of PutnamBench artifact putnam_1964_a1:
  among six distinct points in the Euclidean plane, the ratio of the longest
  pairwise distance to the shortest is at least the square root of 3. This
  file contains no proof.
*)

let statement =
  `let edist =
     \(x:real#real) (y:real#real).
       sqrt ((FST x - FST y) pow 2 + (SND x - SND y) pow 2) in
   let pair_dists =
     \(A:(real#real)->bool).
       {r | ?a b:real#real.
              a IN A /\ b IN A /\ ~(a = b) /\ r = edist a b} in
   let is_greatest =
     \(s:real->bool) (x:real).
       x IN s /\ (!y. y IN s ==> y <= x) in
   let is_least =
     \(s:real->bool) (x:real).
       x IN s /\ (!y. y IN s ==> x <= y) in
   !A:(real#real)->bool.
     A HAS_SIZE 6
     ==> ?D d:real.
           is_greatest (pair_dists A) D /\
           is_least (pair_dists A) d /\
           D / d >= sqrt (&3)`;;
