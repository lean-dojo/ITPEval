(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_543:
  the number of natural divisors of 30^4, minus 2, is 123. This file contains
  no proof.
*)

let statement =
  `CARD {d:num | d divides (30 EXP 4)} - 2 = 123`;;
