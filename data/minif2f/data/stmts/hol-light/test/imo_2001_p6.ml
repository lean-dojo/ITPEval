(*
  Statement-only formalization of miniF2F test problem imo_2001_p6. This file contains no proof.
*)

let statement =
  `!a b c d:num.
     0 < a /\ 0 < b /\ 0 < c /\ 0 < d /\
     d < c /\ c < b /\ b < a /\
     a * c + b * d =
       (b + d + a - c) * (b + d + c - a)
     ==> ~(prime (a * b + c * d))`;;
