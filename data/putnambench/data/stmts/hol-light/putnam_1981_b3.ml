(*
  Statement-only formalization of PutnamBench artifact putnam_1981_b3:
  unboundedly many natural numbers whose prime divisors of n^2 + 3 also
  divide k^2 + 3 for some natural k with k^2 < n. This file contains no proof.
*)

let statement =
  `let P =
     \n:num.
       !p:num.
         prime p /\ p divides (n EXP 2 + 3)
         ==> ?k:num.
               k EXP 2 < n /\
               p divides (k EXP 2 + 3) in
   !n:num. ?m:num. m > n /\ P m`;;
