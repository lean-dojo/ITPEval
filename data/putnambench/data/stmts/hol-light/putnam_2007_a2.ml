(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2007_a2:
  the least possible Lebesgue area of a convex planar set meeting both
  branches of each hyperbola xy = 1 and xy = -1 is 4. This file contains no
  proof.
*)

let statement =
  `let convex_planar =
     \(S:(real#real)->bool).
       !p q:real#real.
         p IN S /\ q IN S
         ==> !t:real.
               &0 <= t /\ t <= &1
               ==> ((&1 - t) * FST p + t * FST q,
                    (&1 - t) * SND p + t * SND q) IN S in
   let meets_all_branches =
     \(S:(real#real)->bool).
       (?p:real#real.
          p IN S /\
          &0 < FST p /\ &0 < SND p /\ FST p * SND p = &1) /\
       (?p:real#real.
          p IN S /\
          FST p < &0 /\ SND p < &0 /\ FST p * SND p = &1) /\
       (?p:real#real.
          p IN S /\
          FST p < &0 /\ &0 < SND p /\ FST p * SND p = -- &1) /\
       (?p:real#real.
          p IN S /\
          &0 < FST p /\ SND p < &0 /\ FST p * SND p = -- &1) in
   let cover_bound =
     \(S:(real#real)->bool) (B:real).
       &0 <= B /\
       ?xl xu yl yu:num->real.
         (!k:num. xl k <= xu k /\ yl k <= yu k) /\
         (!p:real#real.
            p IN S
            ==> ?k:num.
                  xl k < FST p /\ FST p < xu k /\
                  yl k < SND p /\ SND p < yu k) /\
         (!N:num.
            sum (0..N)
              (\k:num.
                 (xu k - xl k) * (yu k - yl k)) <= B) in
   let has_finite_area =
     \(S:(real#real)->bool) (area:real).
       (?B:real. cover_bound S B) /\
       area = inf {B:real | cover_bound S B} in
   let admissible =
     \(S:(real#real)->bool).
       convex_planar S /\ meets_all_branches S in
   (?S:(real#real)->bool. admissible S /\ has_finite_area S (&4)) /\
   (!y:real.
      (?S:(real#real)->bool. admissible S /\ has_finite_area S y)
      ==> &4 <= y)`;;
