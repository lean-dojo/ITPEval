(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_521. This file
  contains no proof.
*)

let statement =
  `!m n:num.
     EVEN m /\
     EVEN n /\
     m - n = 2 /\
     m * n = 288
     ==> m = 18`;;
