(*
  Statement-only formalization of Logipedia corpus artifact nat.eqb_n_n,
  catalog title "nat.eqb_n_n": the Boolean equality test of every natural
  number with itself is true. This file contains no proof.
*)

let logipedia_nat_eqb = new_definition
  `logipedia_nat_eqb (n:num) (m:num) <=> n = m`;;

let statement =
  `!n:num.
     logipedia_nat_eqb n n = T`;;
