(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_483. This file
  contains no proof.
*)

let statement =
  `!a:num->num.
     (a 1 = 1 /\
      a 2 = 1 /\
      (!n:num. a (n + 2) = a (n + 1) + a n))
     ==> a 100 MOD 4 = 3`;;
