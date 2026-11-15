(*
  Statement-only formalization of miniF2F test problem induction_pord1p1on2powklt5on2. This file
  contains no proof.
*)

let statement =
  `!n:num.
     0 < n
     ==> product (1..n) (\k. &1 + &1 / (&2 pow k)) < &5 / &2`;;
