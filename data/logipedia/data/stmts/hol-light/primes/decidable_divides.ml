(*
  Statement-only formalization of Logipedia corpus artifact
  primes.decidable_divides, catalog title "primes.decidable_divides":
  divisibility between any two natural numbers is decidable. This file
  contains no proof.
*)

let statement =
  `!n m:num. n divides m \/ ~(n divides m)`;;
