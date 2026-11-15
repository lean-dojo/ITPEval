(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1993_b3:
  the probability that the nearest integer to x/y is even for a uniformly
  chosen point (x,y) in the open unit square is 5/4 - pi/4. This file
  contains no proof.
*)

needs "Library/transc.ml";;

let statement =
  `let cover_bound =
     \(s:(real#real)->bool) (B:real).
       &0 <= B /\
       ?xl xu yl yu:num->real.
         (!k:num. xl k <= xu k /\ yl k <= yu k) /\
         (!p:real#real.
            p IN s
            ==> ?k:num.
                  xl k < FST p /\ FST p < xu k /\
                  yl k < SND p /\ SND p < yu k) /\
         (!N:num.
            sum (0..N)
              (\k:num. (xu k - xl k) * (yu k - yl k)) <= B) in
   let lebesgue_outer_measure =
     \(s:(real#real)->bool).
       inf {B:real | cover_bound s B} in
   let nearest_integer =
     \x:real.
       @z:int.
         real_of_int z - &1 / &2 <= x /\
         x < real_of_int z + &1 / &2 in
   let putnam_1993_b3_solution =
     (&5 / &4,--(&1 / &4)) in
   lebesgue_outer_measure
     {p:real#real |
        &0 < FST p /\ FST p < &1 /\
        &0 < SND p /\ SND p < &1 /\
        (?k:int.
           nearest_integer (FST p / SND p) = (&2:int) * k)} =
   FST putnam_1993_b3_solution +
   SND putnam_1993_b3_solution * pi`;;
