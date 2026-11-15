(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1984_b3:
  every finite carrier with at least two elements admits a right-cancellative
  binary operation for which no triple is associative. This file contains no
  proof.
*)

let statement =
  `FINITE (UNIV:A->bool) /\
   2 <= CARD (UNIV:A->bool)
   ==>
   ?mul:A->A->A.
     !x y z:A.
       (mul x z = mul y z ==> x = y) /\
       ~(mul x (mul y z) = mul (mul x y) z)`;;
