(*
  Statement-only formalization of miniF2F valid artifact amc12a_2010_p11:
  a real exponential equation and a logarithm-base relation determine the
  positive base b as 8/7. This file contains no proof.
*)

needs "Library/transc.ml";;

let statement =
  `!x b:real.
     &0 < b /\
     exp ((x + &7) * ln (&7)) = exp (x * ln (&8)) /\
     x = ln ((&7) pow 7) / ln b
     ==> b = &8 / &7`;;
