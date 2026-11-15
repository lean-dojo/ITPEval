(*
  Statement-only formalization of Logipedia corpus artifact nat.not_lt_to_le,
  catalog title "nat.not_lt_to_le": for all natural numbers n and m, if n is
  not strictly less than m, then m is at most n. This file contains no proof.
*)

let statement =
  `!n m:num. ~(n < m) ==> m <= n`;;
