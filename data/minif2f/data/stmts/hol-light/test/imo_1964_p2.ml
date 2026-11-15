(*
  Statement-only formalization of miniF2F test problem imo_1964_p2. This file contains no proof.
*)

let statement =
  `!a b c:real.
     &0 < a /\ &0 < b /\ &0 < c /\
     c < a + b /\ b < a + c /\ a < b + c
     ==> a pow 2 * (b + c - a) +
         b pow 2 * (c + a - b) +
         c pow 2 * (a + b - c) <= &3 * a * b * c`;;
