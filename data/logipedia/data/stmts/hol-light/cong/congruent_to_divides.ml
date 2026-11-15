(*
  Statement-only formalization of Logipedia corpus artifact
  cong.congruent_to_divides, catalog title "cong.congruent_to_divides":
  congruent natural numbers modulo a positive natural modulus have a
  difference divisible by that modulus. This file contains no proof.
*)

let statement =
  `!n m p:num.
     0 < p
     ==> n MOD p = m MOD p
     ==> p divides (n - m)`;;
