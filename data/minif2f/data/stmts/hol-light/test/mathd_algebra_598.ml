(*
  Statement-only formalization of miniF2F test problem mathd_algebra_598. This file contains no
  proof.
*)

let statement =
  `!a:real b:real c:real d:real.
     exp (a * ln (&4)) = &5 ==>
     exp (b * ln (&5)) = &6 ==>
     exp (c * ln (&6)) = &7 ==>
     exp (d * ln (&7)) = &8 ==>
     a * b * c * d = &3 / &2`;;
