(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2010_a4:
  for every positive integer n, the number
  10^(10^(10^n)) + 10^(10^n) + 10^n - 1 is not prime. This file contains no proof.
*)

let statement =
  `!n:num.
     0 < n
     ==> ~(prime
            (10 EXP (10 EXP (10 EXP n)) +
             10 EXP (10 EXP n) +
             10 EXP n - 1))`;;
