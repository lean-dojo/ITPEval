(*
  Statement-only formalization of Logipedia corpus artifact nat.le_n_Sn,
  catalog title "nat.le_n_Sn": every natural number is less than or equal to
  its successor. This file contains no proof.
*)

let statement =
  `!n:num. n <= SUC n`;;
