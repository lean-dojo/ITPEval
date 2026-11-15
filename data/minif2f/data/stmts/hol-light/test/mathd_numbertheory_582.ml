(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_582. This file
  contains no proof.
*)

let statement =
  `!n:num.
     0 < n /\
     3 divides n
     ==> ((n + 4) + (n + 6) + (n + 8)) MOD 9 = 0`;;
