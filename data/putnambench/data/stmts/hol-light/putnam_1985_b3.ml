(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1985_b3:
  a positive-integer array in which every positive integer occurs exactly
  eight times has an entry a(m,n) greater than m * n at positive indices.
  This file contains no proof.
*)

let statement =
  `!a:num->num->num.
     (!m n:num. 0 < a m n) /\
     (!k:num.
        0 < k
        ==> {(m,n):num#num |
               0 < m /\ 0 < n /\ a m n = k}
            HAS_SIZE 8)
     ==> ?m n:num.
           0 < m /\ 0 < n /\ a m n > m * n`;;
