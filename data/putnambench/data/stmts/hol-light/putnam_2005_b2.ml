(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2005_b2:
  classification of the positive integer tuples whose sum is 5n - 4 and
  whose reciprocal sum is one. This file contains no proof.
*)

let statement =
  `!n:num. !k:num->num.
     (0 < n /\
      (!i:num. i IN (0..n - 1) ==> 0 < k i) /\
      nsum (0..n - 1) (\i:num. k i) = 5 * n - 4 /\
      sum (0..n - 1) (\i:num. &1 / &(k i)) = &1)
     <=>
     (n = 1 /\ k 0 = 1) \/
     (n = 3 /\ IMAGE k (0..2) = {2,3,6}) \/
     (n = 4 /\ (!i:num. i IN (0..3) ==> k i = 4))`;;
