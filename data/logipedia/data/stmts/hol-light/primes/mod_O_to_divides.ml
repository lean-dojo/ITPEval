(*
  Statement-only formalization of Logipedia corpus artifact
  primes.mod_O_to_divides, catalog title "primes.mod_O_to_divides": a positive
  natural number is a divisor of any natural number whose remainder modulo it
  is zero. This file contains no proof.
*)

let statement =
  `!n m:num.
     0 < n
     ==> m MOD n = 0
     ==> n divides m`;;
