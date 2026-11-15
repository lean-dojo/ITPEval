(*
  Statement-only formalization of Logipedia corpus artifact
  primes.divides_to_le, catalog title "primes.divides_to_le": for natural
  numbers n and m, if m is positive and n divides m, then n is at most m.
  This file contains no proof.
*)

let statement =
  `!n m:num.
     0 < m
     ==> n divides m
     ==> n <= m`;;
