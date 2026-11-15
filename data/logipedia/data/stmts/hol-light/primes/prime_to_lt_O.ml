(*
  Statement-only formalization of Logipedia corpus artifact
  primes.prime_to_lt_O, catalog title "primes.prime_to_lt_O": every natural
  number that is prime is strictly positive. This file contains no proof.
*)

let statement =
  `!p:num. prime p ==> 0 < p`;;
