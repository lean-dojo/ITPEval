(*
  Statement-only formalization of Logipedia corpus artifact nat.nat_elim2,
  catalog title "nat.nat_elim2": two-dimensional elimination on natural
  numbers from all pairs (0,n), all pairs (SUC n,0), and a diagonal successor
  step. This file contains no proof.
*)

let statement =
  `!R:num->num->bool.
     (!n:num. R 0 n)
     ==> (!n:num. R (SUC n) 0)
     ==> (!n m:num. R n m ==> R (SUC n) (SUC m))
     ==> !n m:num. R n m`;;
