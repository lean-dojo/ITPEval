(*
  Statement-only formalization of Logipedia corpus artifact nat.minus_S_S,
  catalog title "nat.minus_S_S": for all natural numbers n and m, subtracting
  the successor of m from the successor of n equals n minus m under truncated
  natural subtraction. This file contains no proof.
*)

let statement =
  `!n m:num. (SUC n) - (SUC m) = n - m`;;
