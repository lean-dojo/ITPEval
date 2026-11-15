(*
  Statement-only formalization of Logipedia corpus artifact
  primes.eq_mod_to_divides, catalog title "primes.eq_mod_to_divides":
  natural numbers with equal remainders modulo a positive natural modulus
  have a truncated difference divisible by that modulus. This file contains
  no proof.
*)

let statement =
  `!n m q:num.
     0 < q
     ==> n MOD q = m MOD q
     ==> q divides (n - m)`;;
