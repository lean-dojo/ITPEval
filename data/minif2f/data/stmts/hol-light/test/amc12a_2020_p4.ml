(*
  Statement-only formalization of miniF2F test problem amc12a_2020_p4:
  there are 100 four-digit multiples of five whose digits are all even.
  This file contains no proof.
*)

let statement =
  `CARD
     {n:num |
       ?a b c d:num.
         1 <= a /\ a <= 9 /\ EVEN a /\
         b <= 9 /\ EVEN b /\
         c <= 9 /\ EVEN c /\
         d <= 9 /\ EVEN d /\
         n = 1000 * a + 100 * b + 10 * c + d /\
         5 divides n} = 100`;;
