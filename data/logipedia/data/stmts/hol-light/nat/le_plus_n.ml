(*
  Statement-only formalization of Logipedia corpus artifact nat.le_plus_n,
  catalog title "nat.le_plus_n": every natural number m is less than or equal
  to n + m for every natural number n. This file contains no proof.
*)

let statement =
  `!n m:num. m <= n + m`;;
