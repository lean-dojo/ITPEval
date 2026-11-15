(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2022_a3
  (putnambench__hol-light__putnam_2022_a3): for a prime p greater than 5, the
  number of infinite sequences of nonzero residues modulo p satisfying
  a(n) * a(n+2) = 1 + a(n+1) modulo p is congruent to 0 or 2 modulo 5.
  This file contains no proof.
*)

let statement =
  `!p f:num.
     prime p /\
     p > 5 /\
     f =
       CARD
         {a:num->num |
            (!n:num. 0 < a n /\ a n < p) /\
            (!n:num.
               (a n * a (n + 2)) MOD p =
               (1 + a (n + 1)) MOD p)}
     ==>
     f MOD 5 = 0 \/ f MOD 5 = 2`;;
