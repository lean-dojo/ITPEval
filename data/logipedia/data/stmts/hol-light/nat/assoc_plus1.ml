(*
  Statement-only formalization of Logipedia corpus artifact nat.assoc_plus1,
  catalog title "nat.assoc_plus1": for all natural numbers a, b, and c, the
  nested sum c + (b + a) equals (b + c) + a. This file contains no proof.
*)

let statement =
  `!a b c:num. c + (b + a) = (b + c) + a`;;
