(*
  Statement-only formalization of PutnamBench artifact putnam_1967_b1:
  the midpoints of three alternating sides of a cyclic hexagon form an
  equilateral triangle under the stated side-length and ordering conditions.
  This file contains no proof.
*)

let statement =
  `let edist =
     \(x:real#real) (y:real#real).
       sqrt ((FST x - FST y) pow 2 + (SND x - SND y) pow 2) in
   let midpoint =
     \(x:real#real) (y:real#real).
       ((FST x + FST y) / &2, (SND x + SND y) / &2) in
   let segment =
     \(a:real#real) (b:real#real) (x:real#real).
       ?t:real.
         &0 <= t /\ t <= &1 /\
         FST x = (&1 - t) * FST a + t * FST b /\
         SND x = (&1 - t) * SND a + t * SND b in
   let convex_hull6 =
     \(L:num->real#real) (x:real#real).
       ?a0 a1 a2 a3 a4 a5:real.
         &0 <= a0 /\ &0 <= a1 /\ &0 <= a2 /\
         &0 <= a3 /\ &0 <= a4 /\ &0 <= a5 /\
         a0 + a1 + a2 + a3 + a4 + a5 = &1 /\
         FST x =
           a0 * FST (L 0) + a1 * FST (L 1) + a2 * FST (L 2) +
           a3 * FST (L 3) + a4 * FST (L 4) + a5 * FST (L 5) /\
         SND x =
           a0 * SND (L 0) + a1 * SND (L 1) + a2 * SND (L 2) +
           a3 * SND (L 3) + a4 * SND (L 4) + a5 * SND (L 5) in
   let interior =
     \(S:(real#real)->bool) (x:real#real).
       ?e:real.
         &0 < e /\
         !y:real#real. edist x y < e ==> S y in
   !r:real. !L:num->real#real. !P Q R:real#real.
     P = midpoint (L 1) (L 2) /\
     Q = midpoint (L 3) (L 4) /\
     R = midpoint (L 5) (L 0) /\
     r > &0 /\
     (?O:real#real.
        !i:num. i < 6 ==> edist O (L i) = r) /\
     (!i j:num.
        i < 6 /\ j < 6 /\ ~(i = j)
        ==> (i + 1) MOD 6 = j \/
            i = (j + 1) MOD 6 \/
            ?x:real#real.
              segment (L i) (L j) x /\ interior (convex_hull6 L) x) /\
     edist (L 0) (L 1) = r /\
     edist (L 2) (L 3) = r /\
     edist (L 4) (L 5) = r /\
     ~(L 1 = L 2) /\
     ~(L 3 = L 4) /\
     ~(L 5 = L 0)
     ==> edist P Q = edist R P /\ edist Q R = edist P Q`;;
