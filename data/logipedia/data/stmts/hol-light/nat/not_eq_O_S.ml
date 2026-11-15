(*
  Statement-only formalization of Logipedia corpus artifact nat.not_eq_O_S,
  catalog title "nat.not_eq_O_S": zero is not equal to the successor of any
  natural number. This file contains no proof.
*)

let statement =
  `!n:num. ~(0 = SUC n)`;;
