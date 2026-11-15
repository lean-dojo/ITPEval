(*
  Statement-only formalization of Logipedia corpus artifact
  nat.le_to_le_to_eq, catalog title "nat.le_to_le_to_eq": antisymmetry of
  less-than-or-equal on natural numbers. This file contains no proof.
*)

let statement =
  `!n m:num. n <= m ==> m <= n ==> n = m`;;
