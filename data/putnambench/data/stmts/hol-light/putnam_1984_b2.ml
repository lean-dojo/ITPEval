(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1984_b2:
  the minimum value 8 of a two-variable sum of squares on the domain
  0 < u < sqrt 2 and v > 0. This file contains no proof.
*)

let statement =
  `let feasible =
     \u v:real.
       &0 < u /\ u < sqrt (&2) /\ &0 < v in
   let objective =
     \u v:real.
       (u - v) pow 2 +
       (sqrt (&2 - u pow 2) - &9 / v) pow 2 in
   let solution = &8 in
   (!u v:real.
      feasible u v
      ==> solution <= objective u v) /\
   (?u v:real.
      feasible u v /\
      objective u v = solution)`;;
