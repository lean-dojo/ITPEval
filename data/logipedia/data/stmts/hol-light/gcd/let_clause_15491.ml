(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.let_clause_15491, catalog title "gcd.let_clause_15491": for arbitrary
  natural numbers m and n, if n is zero, then subtracting n from any natural
  number leaves it unchanged. This file contains no proof.
*)

let statement =
  `!m:num. !n:num.
     0 = n
     ==> !x1106:num.
           x1106 = x1106 - n`;;
