(*
  Statement-only formalization of Logipedia corpus artifact
  nat.le_to_lt_to_lt, catalog title "nat.le_to_lt_to_lt": mixed transitivity
  of natural-number order, from n <= m and m < p to n < p. This file contains
  no proof.
*)

let statement =
  `!n m p:num. n <= m ==> m < p ==> n < p`;;
