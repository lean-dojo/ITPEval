(*
  Statement-only formalization of miniF2F test problem imo_1983_p6. This file contains no proof.
*)

let statement =
  `!a b c:real.
     &0 < a /\ &0 < b /\ &0 < c /\
     c < a + b /\ b < a + c /\ a < b + c
     ==> &0 <= a pow 2 * b * (a - b) +
                b pow 2 * c * (b - c) +
                c pow 2 * a * (c - a)`;;
