(*
  Statement-only formalization of Logipedia corpus artifact nat.le_plus_n_r,
  catalog title "nat.le_plus_n_r": every natural number m is less than or
  equal to m + n for every natural number n. This file contains no proof.
*)

let statement =
  `!n m:num. m <= m + n`;;
