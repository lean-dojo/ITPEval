(*
  Statement-only formalization of miniF2F valid artifact mathd_algebra_493:
  a real function satisfying f(x) = x^2 - 4 * sqrt(x) + 1 has
  f(f(4)) = 70. This file contains no proof.
*)

let statement =
  `!f:real->real.
     (!x:real. f x = x pow 2 - &4 * sqrt x + &1)
     ==> f (f (&4)) = &70`;;
