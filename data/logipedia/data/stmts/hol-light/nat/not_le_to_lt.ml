(*
  Statement-only formalization of Logipedia corpus artifact nat.not_le_to_lt,
  catalog title "nat.not_le_to_lt": for all natural numbers n and m, if n is
  not at most m, then m is strictly less than n. This file contains no proof.
*)

let statement =
  `!n m:num. ~(n <= m) ==> m < n`;;
