(*
  Statement-only formalization of Logipedia corpus artifact nat.minus_plus_m_m,
  catalog title "nat.minus_plus_m_m": adding any natural number m to a natural
  number n and then subtracting m using truncated natural subtraction yields n.
  This file contains no proof.
*)

let statement =
  `!n m:num. n = (n + m) - m`;;
