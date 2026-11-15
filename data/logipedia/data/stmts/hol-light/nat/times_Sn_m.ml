(*
  Statement-only formalization of Logipedia corpus artifact nat.times_Sn_m,
  catalog title "nat.times_Sn_m": for all natural numbers n and m, adding m
  to n multiplied by m equals the successor of n multiplied by m. This file
  contains no proof.
*)

let statement =
  `!n m:num. m + n * m = SUC n * m`;;
