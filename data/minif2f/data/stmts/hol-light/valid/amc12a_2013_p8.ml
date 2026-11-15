(*
  Statement-only formalization of miniF2F valid problem amc12a_2013_p8. This file contains no
  proof.
*)

let amc12a_2013_p8 =
  `!x y:real.
     ~(x = &0) /\
     ~(y = &0) /\
     ~(x = y) /\
     x + &2 / x = y + &2 / y
     ==> x * y = &2`;;
