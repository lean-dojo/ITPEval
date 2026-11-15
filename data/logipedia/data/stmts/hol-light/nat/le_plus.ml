(*
  Statement-only formalization of Logipedia corpus artifact nat.le_plus,
  catalog title "nat.le_plus": addition is monotone in both arguments on the
  natural numbers. This file contains no proof.
*)

let statement =
  `!n1 n2 m1 m2:num.
     n1 <= n2
     ==>
     m1 <= m2
     ==>
     n1 + m1 <= n2 + m2`;;
