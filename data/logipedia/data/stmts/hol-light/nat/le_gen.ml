(*
  Statement-only formalization of Logipedia corpus artifact nat.le_gen,
  catalog title "nat.le_gen": any predicate that holds for every natural
  number at most n holds at n. This file contains no proof.
*)

let statement =
  `!P:num->bool. !n:num.
     (!i:num. i <= n ==> P i)
     ==> P n`;;
