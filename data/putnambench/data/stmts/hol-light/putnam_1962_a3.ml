(*
  Statement-only formalization of PutnamBench artifact putnam_1962_a3:
  the area ratio of the triangle formed by the pairwise intersections of
  three cevians determined by a common positive side-division ratio.
  This file contains no proof.
*)

let statement =
  `let edist =
     \(x:real#real) (y:real#real).
       sqrt ((FST x - FST y) pow 2 + (SND x - SND y) pow 2) in
   let on_segment =
     \(x:real#real) (a:real#real) (b:real#real).
       ?t:real.
         &0 <= t /\ t <= &1 /\
         FST x = (&1 - t) * FST a + t * FST b /\
         SND x = (&1 - t) * SND a + t * SND b in
   let triangle_area =
     \(a:real#real) (b:real#real) (c:real#real).
       abs ((FST b - FST a) * (SND c - SND a) -
            (SND b - SND a) * (FST c - FST a)) / &2 in
   !A B C A' B' C' P Q R:real#real. !k:real.
     &0 < k /\
     ~((FST B - FST A) * (SND C - SND A) =
       (SND B - SND A) * (FST C - FST A)) /\
     on_segment A' B C /\
     edist C A' / edist A' B = k /\
     on_segment B' C A /\
     edist A B' / edist B' C = k /\
     on_segment C' A B /\
     edist B C' / edist C' A = k /\
     on_segment P B B' /\
     on_segment P C C' /\
     on_segment Q C C' /\
     on_segment Q A A' /\
     on_segment R A A' /\
     on_segment R B B'
     ==> triangle_area P Q R / triangle_area A B C =
         (k - &1) pow 2 / (k pow 2 + k + &1)`;;
