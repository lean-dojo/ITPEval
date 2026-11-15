(*
  Statement-only formalization of Logipedia corpus artifact nat.not_le_Sn_O,
  catalog title "nat.not_le_Sn_O": no successor natural number is at most
  zero. This file contains no proof.
*)

let statement =
  `!n:num. ~(SUC n <= 0)`;;
