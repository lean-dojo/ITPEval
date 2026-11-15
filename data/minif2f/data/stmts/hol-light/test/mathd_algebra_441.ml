(*
  Statement-only formalization of miniF2F test problem mathd_algebra_441. This file contains no
  proof.
*)

let statement =
  `!x:real.
     ~(x = &0)
     ==> &12 / (x * x) * (x pow 4 / (&14 * x)) * (&35 / (&3 * x)) = &10`;;
