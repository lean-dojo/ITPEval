(*
  Statement-only formalization of Logipedia corpus artifact
  nat.le_to_or_lt_eq, catalog title "nat.le_to_or_lt_eq": every
  natural-number inequality n <= m yields either n < m or n = m. This file
  contains no proof.
*)

let statement =
  `!n m:num. n <= m ==> n < m \/ n = m`;;
