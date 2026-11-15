(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2024_b1:
  the positive grid sizes and offsets admitting a nonattacking selection whose
  entries are exactly the integers from 1 through the grid size. This file
  contains no proof.
*)

let statement =
  `!n k:num.
     (0 < n /\
      0 < k /\
      ?f:num->num.
        IMAGE f (1..n) = (1..n) /\
        IMAGE (\i. (&i:int) + &(f i) - &k) (1..n) =
        {z:int | (&1:int) <= z /\ z <= &n})
     <=>
     ?l:num. n = 2 * l + 1 /\ k = l + 1`;;
