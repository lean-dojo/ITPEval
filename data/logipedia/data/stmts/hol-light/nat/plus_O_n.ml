(*
  Statement-only formalization of Logipedia corpus artifact nat.plus_O_n,
  catalog title "nat.plus_O_n": adding natural zero on the left leaves every
  natural number unchanged. This file contains no proof.
*)

let statement =
  `!n:num. n = 0 + n`;;
