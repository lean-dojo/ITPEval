(*
  Statement-only formalization of miniF2F valid artifact mathd_algebra_510:
  if real numbers x and y have sum 13 and product 24, then
  sqrt(x^2 + y^2) = 11. This file contains no proof.
*)

let statement =
  `!x y:real.
     x + y = &13 /\
     x * y = &24
     ==> sqrt (x pow 2 + y pow 2) = &11`;;
