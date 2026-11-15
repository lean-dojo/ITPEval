(*
  Statement-only formalization of Logipedia corpus artifact
  primes.not_divides_to_dividesb_false, catalog title
  "primes.not_divides_to_dividesb_false": a positive natural number that does
  not divide another has a false modulo-zero divisibility test. This file
  contains no proof.
*)

let logipedia_primes_dividesb = new_definition
  `logipedia_primes_dividesb (n:num) (m:num) <=> m MOD n = 0`;;

let statement =
  `!n m:num.
     0 < n
     ==> ~(n divides m)
     ==> logipedia_primes_dividesb n m = F`;;
