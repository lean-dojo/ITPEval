(*
  Statement-only formalization of Logipedia corpus artifact nat.match_le_prop,
  catalog title "nat.match_le_prop": a predicate holding at a natural n and
  at every successor holds at every natural m with n <= m. This file contains
  no proof.
*)

let statement =
  `!n:num p:num->bool.
     p n
     ==> (!k:num. p (SUC k))
     ==> !m:num. n <= m ==> p m`;;
