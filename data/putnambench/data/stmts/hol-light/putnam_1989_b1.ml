(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1989_b1:
  the area probability that a point in a square is closer to its center than
  to every point on an edge. This file contains no proof.
*)

let statement =
  `let square =
     {p:real#real |
        &0 <= FST p /\ FST p <= &1 /\
        &0 <= SND p /\ SND p <= &1} in
   let edges =
     {p:real#real |
        p IN square /\
        (FST p = &0 \/ FST p = &1 \/
         SND p = &0 \/ SND p = &1)} in
   let center = (&1 / &2,&1 / &2) in
   let squared_distance =
     \(p:real#real) (q:real#real).
       (FST p - FST q) pow 2 + (SND p - SND q) pow 2 in
   let closer =
     {p:real#real |
        p IN square /\
        !q:real#real.
          q IN edges
          ==> squared_distance p center < squared_distance p q} in
   let cover_bound =
     \(s:(real#real)->bool) (B:real).
       &0 <= B /\
       ?left right bottom top:num->real.
         (!k. left k <= right k /\ bottom k <= top k) /\
         (!p. p IN s
              ==> ?k.
                    left k < FST p /\ FST p < right k /\
                    bottom k < SND p /\ SND p < top k) /\
         (!N.
            sum (0..N)
              (\k. (right k - left k) * (top k - bottom k))
            <= B) in
   let outer_area =
     \(s:(real#real)->bool). inf {B:real | cover_bound s B} in
   outer_area closer / outer_area square =
   (&4 * sqrt (&2) - &5) / &3`;;
