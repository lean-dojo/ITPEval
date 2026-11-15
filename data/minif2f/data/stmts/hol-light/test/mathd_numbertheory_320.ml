(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_320. This file
  contains no proof.
*)

let statement =
  `!n:num.
     n < 101 /\ 101 divides (123456 - n)
     ==> n = 34`;;
