(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.divides_mod_to_divides, catalog title "gcd.divides_mod_to_divides":
  for natural numbers p, m, and positive n, if p divides the remainder of m
  modulo n and p divides n, then p divides m. This file contains no proof.
*)

let statement =
  `!p m n:num.
     0 < n
     ==> p divides (m MOD n)
     ==> p divides n
     ==> p divides m`;;
