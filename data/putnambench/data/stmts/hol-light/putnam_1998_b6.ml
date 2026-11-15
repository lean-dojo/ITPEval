(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1998_b6:
  every integer-coefficient monic cubic has a positive integer input at which
  its value is not an integer square. This file contains no proof.
*)

let statement =
  `!a b c:int.
     ?n:int.
       (&0:int) < n /\
       ~(?m:int.
           n pow 3 + a * n pow 2 + b * n + c = m pow 2)`;;
