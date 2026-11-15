(*
  Statement-only formalization of PutnamBench artifact putnam_1973_a1:
  area bounds for a triangle formed by points on the three sides of a
  nondegenerate triangle in the real Euclidean plane. This file contains no
  proof.
*)

let statement =
  `let edist =
     \(p:real#real) (q:real#real).
       sqrt ((FST p - FST q) pow 2 + (SND p - SND q) pow 2) in
   let segment =
     \(p:real#real) (q:real#real) (x:real#real).
       ?t:real.
         &0 <= t /\ t <= &1 /\
         FST x = (&1 - t) * FST p + t * FST q /\
         SND x = (&1 - t) * SND p + t * SND q in
   let det2 =
     \(p:real#real) (q:real#real) (r:real#real).
       (FST q - FST p) * (SND r - SND p) -
       (SND q - SND p) * (FST r - FST p) in
   let triangle_area =
     \(p:real#real) (q:real#real) (r:real#real).
       abs (det2 p q r) / &2 in
   !A B C X Y Z:real#real.
     ~(det2 A B C = &0) /\
     segment B C X /\
     segment C A Y /\
     segment A B Z
     ==>
     (((edist B X <= edist X C /\
        edist C Y <= edist Y A /\
        edist A Z <= edist Z B)
       ==> triangle_area X Y Z >=
           (&1 / &4) * triangle_area A B C) /\
      (triangle_area A Z Y <= triangle_area X Y Z \/
       triangle_area B X Z <= triangle_area X Y Z \/
       triangle_area C Y X <= triangle_area X Y Z))`;;
