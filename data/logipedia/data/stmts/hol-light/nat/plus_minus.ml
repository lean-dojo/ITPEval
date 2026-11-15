(*
  Statement-only formalization of Logipedia corpus artifact nat.plus_minus,
  catalog title "nat.plus_minus": for all natural numbers m, n, and p, if
  m is at most n, then (n - m) + p equals (n + p) - m. This file contains
  no proof.
*)

let statement =
  `!m n p:num. m <= n ==> (n - m) + p = (n + p) - m`;;
