(*
  Statement-only formalization of miniF2F valid problem amc12a_2009_p9. This file contains no
  proof.
*)

let statement =
  `!a:real b:real c:real f:real->real.
     (!x:real. f (x + &3) = &3 * x pow 2 + &7 * x + &4) /\
     (!x:real. f x = a * x pow 2 + b * x + c)
     ==> a + b + c = &2`;;
