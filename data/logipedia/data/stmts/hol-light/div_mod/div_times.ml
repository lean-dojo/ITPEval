(*
  Statement-only formalization of Logipedia corpus artifact div_mod.div_times,
  catalog title "div_mod.div_times": division of a natural-number multiple by
  a positive natural divisor recovers the other factor. This file contains no
  proof.
*)

let statement =
  `!a b:num.
     0 < b
     ==>
     (a * b) DIV b = a`;;
