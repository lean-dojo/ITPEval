(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_12. This file contains
  no proof.
*)

let statement =
  `CARD {x:num | 15 <= x /\ x <= 85 /\ 20 divides x} = 4`;;
