(*
  Statement-only formalization of PutnamBench artifact putnam_1966_b1:
  the sum of the squared side lengths of a convex polygon contained in the
  unit square is at most four. This file contains no proof.
*)

let statement =
  `let edist =
     \(x:real#real) (y:real#real).
       sqrt ((FST x - FST y) pow 2 + (SND x - SND y) pow 2) in
   let collinear3 =
     \(a:real#real) (b:real#real) (c:real#real).
       (FST b - FST a) * (SND c - SND a) =
       (SND b - SND a) * (FST c - FST a) in
   let segment =
     \(a:real#real) (b:real#real) (x:real#real).
       ?t:real.
         &0 <= t /\ t <= &1 /\
         FST x = (&1 - t) * FST a + t * FST b /\
         SND x = (&1 - t) * SND a + t * SND b in
   let polygon_hull =
     \n (L:num->real#real) (x:real#real).
       ?w:num->real.
         (!j. j < n ==> &0 <= w j) /\
         sum (0..n - 1) w = &1 /\
         FST x = sum (0..n - 1) (\j. w j * FST (L j)) /\
         SND x = sum (0..n - 1) (\j. w j * SND (L j)) in
   let hull_interior =
     \n (L:num->real#real) (x:real#real).
       ?e:real.
         &0 < e /\
         !y:real#real. edist x y < e ==> polygon_hull n L y in
   !n:num. !L:num->real#real.
     3 <= n /\
     (!i. i < n
          ==> &0 <= FST (L i) /\ FST (L i) <= &1 /\
              &0 <= SND (L i) /\ SND (L i) <= &1) /\
     (!i j k.
        i < n /\ j < n /\ k < n /\
        ~(i = j) /\ ~(j = k) /\ ~(k = i)
        ==> ~(collinear3 (L i) (L j) (L k))) /\
     (!i. i < n
          ==> ~(?x:real#real.
                  segment (L i) (L ((i + 1) MOD n)) x /\
                  hull_interior n L x))
     ==> sum (0..n - 1)
             (\i. (edist (L i) (L ((i + 1) MOD n))) pow 2) <= &4`;;
