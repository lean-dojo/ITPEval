(*
  Statement-only formalization of Logipedia corpus artifact
  primes.dividesb_false_to_not_divides, catalog title
  "primes.dividesb_false_to_not_divides": a false modulo-zero divisibility
  test implies that one natural number does not divide another. This file
  contains no proof.
*)

let logipedia_primes_dividesb = new_definition
  `logipedia_primes_dividesb (n:num) (m:num) <=> m MOD n = 0`;;

let statement =
  `!n m:num.
     logipedia_primes_dividesb n m = F
     ==> ~(n divides m)`;;
