(*
  Statement-only formalization of Logipedia corpus artifact nat.pred_Sn,
  catalog title "nat.pred_Sn": the predecessor of the successor of every
  natural number is that number. This file contains no proof.
*)

let statement =
  `!n:num. n = PRE (SUC n)`;;
