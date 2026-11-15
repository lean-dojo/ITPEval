(*
  Statement-only formalization of Logipedia corpus artifact
  primes.divides_to_mod_O, catalog title "primes.divides_to_mod_O": a positive
  natural number dividing another natural number implies that the latter has
  remainder zero modulo the former. This file contains no proof.
*)

let statement =
  `!n m:num.
     0 < n
     ==> n divides m
     ==> m MOD n = 0`;;
