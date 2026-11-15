(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_293. This file
  contains no proof.
*)

let statement =
  `!n:num.
     n <= 9 /\ 11 divides (20 * 100 + 10 * n + 7)
     ==> n = 5`;;
