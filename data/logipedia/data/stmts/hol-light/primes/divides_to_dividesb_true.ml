(*
  Statement-only formalization of Logipedia corpus artifact
  primes.divides_to_dividesb_true, catalog title
  "primes.divides_to_dividesb_true": a positive natural divisor makes the
  modulo-zero divisibility test true. This file contains no proof.
*)

let logipedia_primes_dividesb = new_definition
  `logipedia_primes_dividesb (n:num) (m:num) <=> m MOD n = 0`;;

let statement =
  `!n m:num.
     0 < n
     ==> n divides m
     ==> logipedia_primes_dividesb n m = T`;;
