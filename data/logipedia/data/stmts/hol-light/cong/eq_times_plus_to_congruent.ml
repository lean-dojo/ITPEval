(*
  Statement-only formalization of Logipedia corpus artifact
  cong.eq_times_plus_to_congruent, catalog title
  "cong.eq_times_plus_to_congruent": if a natural number is a natural
  multiple of a positive modulus plus another natural number, then the two
  numbers are congruent modulo that modulus. This file contains no proof.
*)

let statement =
  `!n m p r:num.
     0 < p
     ==> n = r * p + m
     ==> n MOD p = m MOD p`;;
