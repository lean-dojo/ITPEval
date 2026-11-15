(*
  Statement-only formalization of Logipedia corpus artifact nat.le_S_S,
  catalog title "nat.le_S_S": the successor operation preserves the
  natural-number order relation. This file contains no proof.
*)

let statement =
  `!n m:num. n <= m ==> SUC n <= SUC m`;;
