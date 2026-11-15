(*
  Statement-only formalization of PutnamBench artifact putnam_1978_b4:
  arbitrarily large integers satisfying the equation equating their sum of
  squares with the sum of their four triple products. This file contains no proof.
*)

let statement =
  `!N:real.
     ?a b c d:int.
       N < real_of_int a /\
       N < real_of_int b /\
       N < real_of_int c /\
       N < real_of_int d /\
       a pow 2 + b pow 2 + c pow 2 + d pow 2 =
       a * b * c + a * b * d + a * c * d + b * c * d`;;
