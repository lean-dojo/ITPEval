(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.let_clause_1549, catalog title "gcd.let_clause_1549": for natural
  numbers m and n, if n is positive and m is zero, then subtracting m from
  any natural number leaves it unchanged. This file contains no proof.
*)

let statement =
  `!m n:num.
     0 < n
     ==> 0 = m
     ==> !x1106:num.
           x1106 = x1106 - m`;;
