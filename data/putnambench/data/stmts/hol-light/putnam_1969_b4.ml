(*
  Statement-only formalization of PutnamBench artifact putnam_1969_b4:
  every continuous plane curve on the unit interval with total variation one
  is contained in a closed rectangle of area one quarter. This file contains
  no proof.
*)

let statement =
  `let vsub =
     \(p:real#real) (q:real#real).
       (FST p - FST q,SND p - SND q) in
   let dot =
     \(u:real#real) (v:real#real).
       FST u * FST v + SND u * SND v in
   let edist =
     \(p:real#real) (q:real#real).
       sqrt (dot (vsub p q) (vsub p q)) in
   let continuous_on_unit_interval =
     \(g:real->real#real).
       !x. &0 <= x /\ x <= &1
           ==> !e. &0 < e
                   ==> ?d. &0 < d /\
                           !y. &0 <= y /\ y <= &1 /\ abs (y - x) < d
                               ==> edist (g y) (g x) < e in
   let unit_partition =
     \n (t:num->real).
       1 <= n /\ t 0 = &0 /\ t n = &1 /\
       (!i. i < n ==> t i < t (i + 1)) in
   let has_unit_variation =
     \(g:real->real#real).
       (!n t. unit_partition n t
              ==> sum (0..n - 1) (\i. edist (g (t (i + 1))) (g (t i)))
                  <= &1) /\
       (!e. &0 < e
            ==> ?n t. unit_partition n t /\
                      &1 - e <
                      sum (0..n - 1)
                          (\i. edist (g (t (i + 1))) (g (t i)))) in
   let quadrilateral_hull =
     \(a:real#real) (b:real#real) (c:real#real) (d:real#real)
      (p:real#real).
       ?u v w z:real.
         &0 <= u /\ &0 <= v /\ &0 <= w /\ &0 <= z /\
         u + v + w + z = &1 /\
         FST p = u * FST a + v * FST b + w * FST c + z * FST d /\
         SND p = u * SND a + v * SND b + w * SND c + z * SND d in
   let right_angle =
     \(a:real#real) (b:real#real) (c:real#real).
       dot (vsub a b) (vsub c b) = &0 in
   !g:real->real#real.
     continuous_on_unit_interval g /\
     has_unit_variation g
     ==> ?a b c d:real#real.
       (!x. &0 <= x /\ x <= &1 ==> quadrilateral_hull a b c d (g x)) /\
       edist a b * edist b c = &1 / &4 /\
       right_angle a b c /\
       right_angle b c d /\
       right_angle c d a /\
       right_angle d a b`;;
