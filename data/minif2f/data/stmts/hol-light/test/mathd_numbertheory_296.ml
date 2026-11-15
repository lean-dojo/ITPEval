(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_296. This file
  contains no proof.
*)

let statement = `!n:num.
  2 <= n /\
  (?x:num. x EXP 3 = n) /\
  (?t:num. t EXP 4 = n)
  ==> 4096 <= n`;;
