(*
  Statement-only formalization of miniF2F valid problem amc12a_2017_p2. This file contains no
  proof.
*)

let amc12a_2017_p2 =
  `!x y:real.
     ~(x = &0) /\
     ~(y = &0) /\
     x + y = &4 * (x * y)
     ==> &1 / x + &1 / y = &4`;;
