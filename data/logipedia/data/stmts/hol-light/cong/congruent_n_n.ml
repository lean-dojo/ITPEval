(*
  Statement-only formalization of Logipedia corpus artifact
  cong.congruent_n_n, catalog title "cong.congruent_n_n": every natural
  number is congruent to itself modulo every natural modulus. This file
  contains no proof.
*)

let statement =
  `!n p:num. n MOD p = n MOD p`;;
