(*
  Statement-only formalization of Logipedia corpus artifact
  primes.prime_to_lt_SO, catalog title "primes.prime_to_lt_SO": every natural
  number that is prime is strictly greater than one. This file contains no
  proof.
*)

let statement =
  `!p:num. prime p ==> 1 < p`;;
