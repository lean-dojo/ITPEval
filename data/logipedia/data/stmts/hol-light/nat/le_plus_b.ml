(*
  Statement-only formalization of Logipedia corpus artifact nat.le_plus_b:
  for all natural numbers b, n, and m, (n + b) <= m implies n <= m.
  This file contains no proof.
*)

let NAT_LE_PLUS_B =
  `!b n m:num. n + b <= m ==> n <= m`;;
