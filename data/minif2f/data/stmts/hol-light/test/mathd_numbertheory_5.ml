(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_5. This file contains
  no proof.
*)

let statement = `!n:num.
  10 <= n /\
  (?x:num. x EXP 2 = n) /\
  (?t:num. t EXP 3 = n)
  ==> 64 <= n`;;
