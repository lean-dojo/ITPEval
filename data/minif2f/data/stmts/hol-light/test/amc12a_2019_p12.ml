(*
  Statement-only formalization of miniF2F test problem amc12a_2019_p12. This file contains no
  proof.
*)

let statement =
  `!x y:real.
     &0 < x /\
     &0 < y /\
     ~(x = &1) /\
     ~(y = &1) /\
     ln x / ln (&2) = ln (&16) / ln y /\
     x * y = &64
     ==> (ln (x / y) / ln (&2)) pow 2 = &20`;;
