(*
  Statement-only formalization of PutnamBench artifact putnam_1966_a2:
  the reciprocal-square inequality for the semiperimeter differences of a
  nondegenerate real-plane triangle with inradius r. This file contains no
  proof.
*)

let statement =
  `let edist =
     \(x:real#real) (y:real#real).
       sqrt ((FST x - FST y) pow 2 + (SND x - SND y) pow 2) in
   let collinear3 =
     \(x:real#real) (y:real#real) (z:real#real).
       (FST y - FST x) * (SND z - SND x) =
       (SND y - SND x) * (FST z - FST x) in
   let triangle_hull =
     \(a:real#real) (b:real#real) (c:real#real) (z:real#real).
       ?u v w:real.
         &0 <= u /\ &0 <= v /\ &0 <= w /\
         u + v + w = &1 /\
         FST z = u * FST a + v * FST b + w * FST c /\
         SND z = u * SND a + v * SND b + w * SND c in
   !r a b c p:real. !A B C:real#real.
     a = edist B C /\
     b = edist C A /\
     c = edist A B /\
     p = (edist B C + edist C A + edist A B) / &2 /\
     ~(collinear3 A B C) /\
     (?center:real#real.
        (?!P:real#real. edist center P = r /\ collinear3 P B C) /\
        (?!Q:real#real. edist center Q = r /\ collinear3 Q C A) /\
        (?!R:real#real. edist center R = r /\ collinear3 R A B) /\
        (!Z:real#real. edist center Z <= r ==> triangle_hull A B C Z))
     ==>
     &1 / ((p - a) pow 2) +
     &1 / ((p - b) pow 2) +
     &1 / ((p - c) pow 2) >=
     &1 / (r pow 2)`;;
