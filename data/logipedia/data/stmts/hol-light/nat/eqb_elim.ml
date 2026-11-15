(*
  Statement-only formalization of Logipedia corpus artifact nat.eqb_elim,
  catalog title "nat.eqb_elim": the Boolean equality test on two natural
  numbers satisfies elimination into an arbitrary predicate on Booleans,
  using the equal and unequal cases. This file contains no proof.
*)

let logipedia_nat_eqb = new_definition
  `logipedia_nat_eqb (n:num) (m:num) <=> n = m`;;

let statement =
  `!n m:num.
   !P:bool->bool.
     ((n = m) ==> P T) ==>
     (~(n = m) ==> P F) ==>
     P (logipedia_nat_eqb n m)`;;
