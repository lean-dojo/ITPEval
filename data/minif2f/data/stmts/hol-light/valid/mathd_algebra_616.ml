(*
  Statement-only formalization of miniF2F valid artifact mathd_algebra_616:
  real functions defined by f(x) = x^3 + 2*x + 1 and g(x) = x - 1 satisfy
  f(g(1)) = 1. This file contains no proof.
*)

let statement =
  `!f g:real->real.
     (!x:real. f x = x pow 3 + &2 * x + &1) /\
     (!x:real. g x = x - &1)
     ==> f (g (&1)) = &1`;;
