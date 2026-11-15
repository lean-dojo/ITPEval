(*
  Statement-only formalization of Logipedia corpus artifact
  cong.divides_to_congruent, catalog title "cong.divides_to_congruent":
  a positive natural modulus dividing the difference of two ordered natural
  numbers makes those numbers congruent modulo that modulus. This file
  contains no proof.
*)

let statement =
  `!n m p:num.
     0 < p
     ==> m <= n
     ==> p divides (n - m)
     ==> n MOD p = m MOD p`;;
