(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2000_a2:
  arbitrarily large integers begin runs of three consecutive integers, each
  expressible as a sum of two integer squares. This file contains no proof.
*)

let statement =
  `!n:int.
     ?m:int.
       m > n /\
       (?a b:int. m = a pow 2 + b pow 2) /\
       (?c d:int. m + &1 = c pow 2 + d pow 2) /\
       (?e f:int. m + &2 = e pow 2 + f pow 2)`;;
