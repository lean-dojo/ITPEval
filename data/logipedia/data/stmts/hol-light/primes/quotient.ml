(*
  Statement-only formalization of Logipedia corpus artifact primes.quotient,
  catalog title "primes.quotient": an equality exhibiting a natural number
  as a multiple supplies a quotient witness for divisibility. This file
  contains no proof.
*)

let statement =
  `!n m q:num.
     m = n * q
     ==> n divides m`;;
