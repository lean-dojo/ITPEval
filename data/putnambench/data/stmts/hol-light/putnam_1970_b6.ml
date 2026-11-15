(*
  Statement-only formalization of PutnamBench artifact putnam_1970_b6:
  a nondegenerate ordered quadrilateral tangent to a common circle and having
  area equal to the square root of the product of its side lengths is cyclic.
  This file contains no proof.
*)

let statement =
  `let edist =
     \(x:real#real) (y:real#real).
       sqrt ((FST x - FST y) pow 2 + (SND x - SND y) pow 2) in
   let collinear3 =
     \(x:real#real) (y:real#real) (z:real#real).
       (FST y - FST x) * (SND z - SND x) =
       (SND y - SND x) * (FST z - FST x) in
   let collinear_set =
     \(s:(real#real)->bool).
       !x y z:real#real.
         x IN s /\ y IN s /\ z IN s ==> collinear3 x y z in
   let segment =
     \(a:real#real) (b:real#real) (x:real#real).
       ?t:real.
         &0 <= t /\ t <= &1 /\
         FST x = (&1 - t) * FST a + t * FST b /\
         SND x = (&1 - t) * SND a + t * SND b in
   let quadrilateral_hull =
     \(L:num->real#real) (x:real#real).
       ?a0 a1 a2 a3:real.
         &0 <= a0 /\ &0 <= a1 /\ &0 <= a2 /\ &0 <= a3 /\
         a0 + a1 + a2 + a3 = &1 /\
         FST x =
           a0 * FST (L 0) + a1 * FST (L 1) +
           a2 * FST (L 2) + a3 * FST (L 3) /\
         SND x =
           a0 * SND (L 0) + a1 * SND (L 1) +
           a2 * SND (L 2) + a3 * SND (L 3) in
   let hull_interior =
     \(L:num->real#real) (x:real#real).
       ?e:real.
         &0 < e /\
         !y:real#real. edist x y < e ==> quadrilateral_hull L y in
   let quadrilateral_area =
     \(L:num->real#real).
       abs
         (FST (L 0) * SND (L 1) - SND (L 0) * FST (L 1) +
          FST (L 1) * SND (L 2) - SND (L 1) * FST (L 2) +
          FST (L 2) * SND (L 3) - SND (L 2) * FST (L 3) +
          FST (L 3) * SND (L 0) - SND (L 3) * FST (L 0)) / &2 in
   !L:num->real#real. !S:(real#real)->bool.
     S = {L 0,L 1,L 2,L 3} /\
     CARD S = 4 /\
     (!s:(real#real)->bool.
        s SUBSET S /\ CARD s = 3 ==> ~collinear_set s) /\
     edist (L 0) (L 1) > &0 /\
     edist (L 1) (L 2) > &0 /\
     edist (L 2) (L 3) > &0 /\
     edist (L 3) (L 0) > &0 /\
     (!i:num.
        i < 4
        ==> ~(?x:real#real.
                segment (L i) (L ((i + 1) MOD 4)) x /\
                hull_interior L x)) /\
     (?O:real#real. ?r:real.
        quadrilateral_hull L O /\ r > &0 /\
        (!i:num.
           i < 4
           ==> (?!q:real#real.
                  collinear3 q (L i) (L ((i + 1) MOD 4)) /\
                  edist O q = r))) /\
     quadrilateral_area L =
       sqrt
         (edist (L 0) (L 1) * edist (L 1) (L 2) *
          edist (L 2) (L 3) * edist (L 3) (L 0))
     ==> ?center:real#real. ?radius:real.
           !p:real#real. p IN S ==> edist p center = radius`;;
