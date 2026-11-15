(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2013_b1:
  the finite sum of products two terms apart in the recursively defined
  integer sequence c has value -1. This file contains no proof.
*)

let statement =
  `!c:num->int.
     c 1 = &1 /\
     (!n:num. 0 < n ==> c (2 * n) = c n) /\
     (!n:num. 0 < n ==> c (2 * n + 1) = (-- &1) pow n * c n)
     ==> isum (1..2013) (\n:num. c n * c (n + 2)) = -- &1`;;
