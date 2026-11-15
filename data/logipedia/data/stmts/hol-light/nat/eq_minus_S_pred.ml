(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eq_minus_S_pred, catalog title "nat.eq_minus_S_pred": for all natural
  numbers n and m, subtracting the successor of m from n equals the
  predecessor of n minus m. This file contains no proof.
*)

let statement =
  `!n m:num. n - SUC m = PRE (n - m)`;;
