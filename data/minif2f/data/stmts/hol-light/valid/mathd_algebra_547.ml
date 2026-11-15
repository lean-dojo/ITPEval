(*
  Statement-only formalization of miniF2F valid artifact mathd_algebra_547:
  for real numbers x = 5 and y = 2, sqrt(x^3 - y^2) = 11, equivalently
  sqrt(x^3 - 2^y) = 11 under these assumptions. This file contains no proof.
*)

let statement =
  `!x y:real.
     x = &5 /\
     y = &2
     ==> sqrt (x pow 3 - y pow 2) = &11`;;
