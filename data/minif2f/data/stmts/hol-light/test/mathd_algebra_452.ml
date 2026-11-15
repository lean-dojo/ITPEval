(*
  Statement-only formalization of miniF2F test problem mathd_algebra_452. This file contains no
  proof.
*)

let statement =
  `!a:num->real.
     (!n:num. a (n + 2) - a (n + 1) = a (n + 1) - a n) /\
     a 1 = &2 / &3 /\
     a 9 = &4 / &5
     ==> a 5 = &11 / &15`;;
