(*
  Statement-only formalization of Logipedia corpus artifact
  nat.not_eq_to_le_to_lt, catalog title "nat.not_eq_to_le_to_lt": for natural
  numbers n and m, n is unequal to m and n <= m imply n < m. This file
  contains no proof.
*)

let statement =
  `!n m:num. ~(n = m) ==> n <= m ==> n < m`;;
