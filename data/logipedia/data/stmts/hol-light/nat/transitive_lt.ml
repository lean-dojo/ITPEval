(*
  Statement-only formalization of Logipedia corpus artifact
  nat.transitive_lt, catalog title "nat.transitive_lt": the strict
  natural-number order is transitive. This file contains no proof.
*)

let statement =
  `!a b c:num. a < b ==> b < c ==> a < c`;;
