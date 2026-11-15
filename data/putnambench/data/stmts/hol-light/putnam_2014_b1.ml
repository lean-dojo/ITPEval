(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2014_b1:
  positive integers with a unique base-10 over-expansion are exactly those
  whose significant decimal digits are all nonzero. This file contains no proof.
*)

let statement =
  `let overexpansion =
     \(N:num) (ds:num list).
       ITLIST (\d acc. d + 10 * acc) ds 0 = N /\
       ~(LAST ds = 0) /\
       (!d:num. MEM d ds ==> d <= 10) in
   !S:num->bool.
     (!N:num.
        S N <=>
        0 < N /\ ?!ds:num list. overexpansion N ds)
     ==>
     S =
     {N:num |
        0 < N /\
        (!i:num.
           0 < N DIV (10 EXP i)
           ==> ~((N DIV (10 EXP i)) MOD 10 = 0))}`;;
