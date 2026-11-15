(*
  Statement-only formalization of Logipedia corpus artifact
  primes.dividesb_true_to_divides, catalog title
  "primes.dividesb_true_to_divides": a true modulo-zero divisibility test
  implies that one natural number divides another. This file contains no
  proof.
*)

let logipedia_primes_dividesb = new_definition
  `logipedia_primes_dividesb (n:num) (m:num) <=> m MOD n = 0`;;

let statement =
  `!n m:num.
     logipedia_primes_dividesb n m = T
     ==> n divides m`;;
