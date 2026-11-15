(*
  Statement-only formalization of PutnamBench artifact putnam_1976_b6:
  every natural number whose sum of positive divisors is one more than twice
  the number is the square of an odd integer. This file contains no proof.
*)

let statement =
  `!N:num.
     nsum {d:num | d divides N} (\d. d) = 2 * N + 1
     ==> ?m:num. ODD m /\ m EXP 2 = N`;;
