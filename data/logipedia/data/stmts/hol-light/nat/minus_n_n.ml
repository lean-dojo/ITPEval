(*
  Statement-only formalization of Logipedia corpus artifact nat.minus_n_n,
  catalog title "nat.minus_n_n": subtracting any natural number from itself
  using truncated natural subtraction yields zero. This file contains no proof.
*)

let statement =
  `!n:num. 0 = n - n`;;
