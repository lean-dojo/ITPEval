(*
  Statement-only formalization of Logipedia corpus artifact nat.plus_minus_m_m,
  catalog title "nat.plus_minus_m_m": for natural numbers n and m, if m is at
  most n, then adding m to the truncated difference n minus m recovers n. This
  file contains no proof.
*)

let statement =
  `!n m:num. m <= n ==> n = (n - m) + m`;;
