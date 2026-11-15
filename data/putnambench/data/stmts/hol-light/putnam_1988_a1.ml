(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1988_a1:
  the planar region satisfying |x| - |y| <= 1 and |y| <= 1 has Lebesgue
  area 6. This file contains no proof.
*)

let statement =
  `let cover_bound =
     \(S:real^2->bool) (B:real).
       &0 <= B /\
       ?a b c d:num->real.
         (!k. a k <= b k /\ c k <= d k) /\
         (!p. p IN S
              ==> ?k.
                    a k < p$1 /\ p$1 < b k /\
                    c k < p$2 /\ p$2 < d k) /\
         (!N.
            sum (0..N)
              (\k. (b k - a k) * (d k - c k)) <= B) in
   let outer_area =
     \(S:real^2->bool). inf {B:real | cover_bound S B} in
   let R =
     {p:real^2 |
        abs (p$1) - abs (p$2) <= &1 /\
        abs (p$2) <= &1} in
   outer_area R = &6`;;
