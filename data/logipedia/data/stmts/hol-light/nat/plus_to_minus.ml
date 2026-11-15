(*
  Statement-only formalization of Logipedia corpus artifact nat.plus_to_minus,
  catalog title "nat.plus_to_minus": for all natural numbers n, m, and p, if
  n equals m plus p, then the truncated difference n minus m equals p. This
  file contains no proof.
*)

let statement =
  `!n m p:num. n = m + p ==> n - m = p`;;
