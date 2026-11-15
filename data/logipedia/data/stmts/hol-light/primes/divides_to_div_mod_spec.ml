(*
  Statement-only formalization of Logipedia corpus artifact
  primes.divides_to_div_mod_spec, catalog title
  "primes.divides_to_div_mod_spec": a positive natural divisor of a natural
  number gives a division specification with the natural quotient and zero
  remainder. This file contains no proof.
*)

let logipedia_div_mod_spec = new_definition
  `logipedia_div_mod_spec (a:num) b q r <=>
     r < b /\ a = q * b + r`;;

let statement =
  `!n m:num.
     0 < n
     ==> n divides m
     ==> logipedia_div_mod_spec m n (m DIV n) 0`;;
