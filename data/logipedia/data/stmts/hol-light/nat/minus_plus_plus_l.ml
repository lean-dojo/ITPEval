(*
  Statement-only formalization of Logipedia corpus artifact
  nat.minus_plus_plus_l, catalog title "nat.minus_plus_plus_l": adding the
  same natural number to both arguments of truncated natural subtraction
  leaves the difference unchanged. This file contains no proof.
*)

let statement =
  `!x y h:num. (x + h) - (y + h) = x - y`;;
