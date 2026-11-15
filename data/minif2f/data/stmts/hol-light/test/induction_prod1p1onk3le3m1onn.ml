(*
  Statement-only formalization of miniF2F test problem induction_prod1p1onk3le3m1onn. This file
  contains no proof.
*)

let statement =
  `!n:num.
     0 < n
     ==> product (1..n) (\k. &1 + &1 / ((&k) pow 3))
         <= &3 - &1 / &n`;;
