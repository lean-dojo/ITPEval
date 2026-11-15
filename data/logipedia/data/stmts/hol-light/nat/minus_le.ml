(*
  Statement-only formalization of Logipedia corpus artifact nat.minus_le,
  catalog title "nat.minus_le": truncated subtraction of one natural number
  from another is at most the original number. This file contains no proof.
*)

let statement =
  `!x y:num. x - y <= x`;;
