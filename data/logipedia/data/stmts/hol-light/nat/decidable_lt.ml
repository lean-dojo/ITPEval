(*
  Statement-only formalization of Logipedia corpus artifact nat.decidable_lt,
  catalog title "nat.decidable_lt": the natural-number strict-order proposition
  n < m is decidable for every pair of natural numbers. This file contains
  no proof.
*)

let statement =
  `!n m:num. n < m \/ ~(n < m)`;;
