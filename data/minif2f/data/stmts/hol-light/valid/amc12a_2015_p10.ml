(*
  Statement-only formalization of miniF2F valid problem amc12a_2015_p10. This file contains no
  proof.
*)

let amc12a_2015_p10 =
  `!x y:num.
     0 < y /\
     y < x /\
     x + y + x * y = 80
     ==> x = 26`;;
