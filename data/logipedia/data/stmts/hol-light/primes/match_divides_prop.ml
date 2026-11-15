(*
  Statement-only formalization of Logipedia corpus artifact
  primes.match_divides_prop, catalog title "primes.match_divides_prop": if a
  proposition follows from every natural quotient witness for a divisibility
  relation, divisibility entails that proposition. This file contains no
  proof.
*)

let statement =
  `!n m:num.
   !return_type:bool.
     (!q:num. m = n * q ==> return_type)
     ==> n divides m
     ==> return_type`;;
