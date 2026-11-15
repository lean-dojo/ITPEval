(*
  Statement-only formalization of Logipedia corpus artifact nat.lt_O_S,
  catalog title "nat.lt_O_S": every successor natural number is strictly
  greater than zero. This file contains no proof.
*)

let statement =
  `!n:num. 0 < SUC n`;;
