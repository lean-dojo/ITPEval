(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1997_b3:
  the positive integers for which the reduced denominator of the harmonic
  sum from 1 through n is not divisible by 5. This file contains no proof.
*)

let statement =
  `let solution =
     \n:num.
       (1 <= n /\ n <= 4) \/
       (20 <= n /\ n <= 24) \/
       (100 <= n /\ n <= 104) \/
       (120 <= n /\ n <= 124) in
   !n p q:num.
     0 < n /\
     0 < p /\
     0 < q /\
     coprime(p,q) /\
     sum (1..n) (\m:num. &1 / &m) = &p / &q
     ==> (~(5 divides q) <=> solution n)`;;
