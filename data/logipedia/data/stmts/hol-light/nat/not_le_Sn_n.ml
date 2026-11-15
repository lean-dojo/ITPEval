(*
  Statement-only formalization of Logipedia corpus artifact nat.not_le_Sn_n,
  catalog title "nat.not_le_Sn_n": no successor natural number is less than
  or equal to its predecessor. This file contains no proof.
*)

let statement =
  `!n:num. ~(SUC n <= n)`;;
