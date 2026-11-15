(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2004_b2:
  the normalized factorial at the sum of two positive integers is strictly
  less than the product of their normalized factorials. This file contains no
  proof.
*)

let statement =
  `!m n:num.
     0 < m /\ 0 < n
     ==> &(FACT (m + n)) / (&(m + n) pow (m + n)) <
         (&(FACT m) / (&m pow m)) * (&(FACT n) / (&n pow n))`;;
