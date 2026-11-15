(*
  Statement-only formalization of Logipedia corpus artifact
  nat.transitive_le, catalog title "nat.transitive_le": the natural-number
  order is transitive. This file contains no proof.
*)

let statement =
  `!a b c:num. a <= b ==> b <= c ==> a <= c`;;
