(*
  Statement-only formalization of Logipedia corpus artifact
  nat.minus_le_minus_minus_comm, catalog title
  "nat.minus_le_minus_minus_comm": for natural numbers a, b, and c, if c is
  at most b, then subtracting b minus c from a equals subtracting b from
  a plus c. This file contains no proof.
*)

let statement =
  `!b c a:num. c <= b ==> a - (b - c) = (a + c) - b`;;
