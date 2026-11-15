(*
  Statement-only formalization of Logipedia corpus artifact
  primes.let_clause_1531, catalog title "primes.let_clause_1531": for natural
  numbers n, m, and d, a positive m divisible by n and equal to n times zero
  is equal to zero. This file contains no proof.
*)

let statement =
  `!n m:num.
     0 < m
     ==> n divides m
     ==> !d:num.
           m = n * 0
           ==> m = 0`;;
