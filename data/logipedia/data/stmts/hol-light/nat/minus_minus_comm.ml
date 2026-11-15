(*
  Statement-only formalization of Logipedia corpus artifact
  nat.minus_minus_comm, catalog title "nat.minus_minus_comm": for all natural
  numbers a, b, and c, subtracting b and then c from a equals subtracting c
  and then b. This file contains no proof.
*)

let statement =
  `!a b c:num. (a - b) - c = (a - c) - b`;;
