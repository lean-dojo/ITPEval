(*
  Statement-only formalization of Logipedia corpus artifact bigops.assoc,
  catalog title "bigops.assoc": associativity of multiplication on natural
  numbers. This file contains no proof.
*)

let statement =
  `!a b c:num. a * (b * c) = (a * b) * c`;;
