(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_1124. This file
  contains no proof.
*)

let statement = `!n:num.
  n <= 9 /\
  18 divides (374 * 10 + n)
  ==> n = 4`;;
