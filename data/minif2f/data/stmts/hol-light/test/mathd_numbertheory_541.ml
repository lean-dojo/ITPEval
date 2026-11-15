(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_541. This file
  contains no proof.
*)

let statement =
  `!m n:num.
     1 < m /\
     1 < n /\
     m * n = 2005
     ==> m + n = 406`;;
