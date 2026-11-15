(*
  Statement-only formalization of PutnamBench artifact putnam_1969_b1:
  divisibility by 24 of the sum of all positive divisors of a positive
  integer n when 24 divides n + 1. This file contains no proof.
*)

let statement =
  `!n:num.
     0 < n /\ 24 divides (n + 1)
     ==> 24 divides nsum {d:num | d divides n} (\d. d)`;;
