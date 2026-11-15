(*
  Statement-only formalization of Logipedia corpus artifact nat.le_n_O_elim,
  catalog title "nat.le_n_O_elim": if a natural number is at most zero, every
  predicate holding at zero also holds at that number. This file contains no
  proof.
*)

let statement =
  `!n:num. n <= 0 ==> !P:num->bool. P 0 ==> P n`;;
