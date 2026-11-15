(*
  Statement-only formalization of Logipedia corpus artifact nat.minus_to_plus,
  catalog title "nat.minus_to_plus": for natural numbers n, m, and p, if m is
  at most n and the truncated difference n minus m equals p, then n equals
  m plus p. This file contains no proof.
*)

let statement =
  `!n m p:num. m <= n ==> n - m = p ==> n = m + p`;;
