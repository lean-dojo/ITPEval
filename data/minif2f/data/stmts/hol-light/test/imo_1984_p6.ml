(*
  Statement-only formalization of miniF2F test problem imo_1984_p6: ordered
  positive odd natural numbers whose outer and inner sums are powers of two
  and whose outer and inner products agree. This file contains no proof.
*)

let statement =
  `!a b c d k m:num.
     0 < a /\ 0 < b /\ 0 < c /\ 0 < d /\
     ODD a /\ ODD b /\ ODD c /\ ODD d /\
     a < b /\ b < c /\ c < d /\
     a * d = b * c /\
     a + d = 2 EXP k /\
     b + c = 2 EXP m
     ==> a = 1`;;
